/*
   Based on Neil Kolban example for IDF: https://github.com/nkolban/esp32-snippets/blob/master/cpp_utils/tests/BLE%20Tests/SampleScan.cpp
   Ported to Arduino ESP32 by Evandro Copercini
*/

#include <Arduino.h>
#include "hex_dump.h"
#include "EEPROM.h"
#include "mbedtls/ccm.h"
#include <vector>
#include "soc/rtc_wdt.h"

#include <NimBLEDevice.h> 
#include <NimBLEUtils.h>

#define CIPHER_KEY_LENGTH 256
#define TOKEN_LENGTH      12
#define BEACON_KEY_LENGTH 12
#define EEPROM_SIZE       256
#define AES_KEY_LENGTH    16
#define NONCE_LENGTH      13

int scanTime = 5; //In seconds
NimBLEScan* pBLEScan;

// Set to NULL for pair process
static NimBLEAddress *pServerAddress = NULL;// new BLEAddress("f8:24:41:ed:01:1d");


static NimBLEUUID uuidXiaomiService("fe95");


static NimBLEUUID uuidAuthCharacteristic("0001");
static NimBLEUUID uuidFwVersionCharacteristic("0004");
static NimBLEUUID uuidAuthInitCharacteristic("0010");
static NimBLEUUID uuidBeaconKeyCharacteristic("0014");

static NimBLEUUID uuidAuthDescriptor("2902");

static uint8_t miAuthStart[]    = {0x90, 0xCA, 0x85, 0xDE};
static uint8_t miAuthConfirm[]  = {0x92, 0xAB, 0x54, 0xFA};

// Notifications status
static uint8_t notificationOn[] = {0x1, 0x0};
static uint8_t notificationOff[] = {0x0, 0x0};

/*
  Product id of device that allowed to pair with us
  For reference:
  0x0153: YLYK01YL
  0x068E: YLYK01YL-FANCL
  0x04E6: YLYK01YL-VENFAN
*/
static uint16_t requiredProductId =0x153;
#define ESP_BD_ADDR_LEN     6
static uint8_t reversedMac[ESP_BD_ADDR_LEN];

static uint8_t cypherKey[CIPHER_KEY_LENGTH];

// Paired device secret beacon key, received after auth or stored to EEPROM
static uint8_t beaconKey[BEACON_KEY_LENGTH];

// AES encryption key to decrypt packets
static uint8_t aesKey[AES_KEY_LENGTH] = { 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x8d, 0x3d, 0x3c, 0x97, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0 };

// Indicate that first phase of auth has been completed
bool bPreAauthDone = false;

// Indicates that we have paired device (from EEPROM or by scan) and do not need to auth
bool bPaired = false;

// Ignore stored beacon key and for device to be paired
bool bForcePair = false;

// TODO: generate token authomatically on auth, instead of static data
// Can be any
static uint8_t token[TOKEN_LENGTH] = { 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xab};

NimBLERemoteCharacteristic* pAuthCharacteristic;
NimBLERemoteCharacteristic* pAuthInitCharacteristic;
NimBLERemoteCharacteristic* pFwVersionCharacteristic;
NimBLERemoteCharacteristic* pBeaconKeyCharacteristic;

class MyAdvertisedDeviceCallbacks: public NimBLEAdvertisedDeviceCallbacks {
    void onResult(NimBLEAdvertisedDevice* advertisedDevice) {
      
      if (advertisedDevice->haveManufacturerData()) {
        	std::string mData = advertisedDevice->getManufacturerData();
          if (mData.length()>4 && mData.substr(0,4) == "\x64\x01\x64\x01") {
            //Serial.printf("Advertised Device: %s \n", advertisedDevice.toString().c_str());
            Serial.printf("Found! [%s], RSSI:%d, Address:%s\n\n", advertisedDevice->getName().c_str(), advertisedDevice->getRSSI(), advertisedDevice->getAddress().toString().c_str());
            
            std::string serviceData = advertisedDevice->getServiceData();
            const char * sData = serviceData.data();
            std::size_t sDataLen = serviceData.length();

            if (sDataLen < 5) { 
              Serial.printf("Invalid service data length has=%d, expect minimum 5", sDataLen);
              return;
            }
            
            uint16_t frameControl = (sData[1]<< 8) + sData[0] ;
            uint16_t productId    = (sData[3]<< 8) + sData[2] ;
            uint32_t frameCounter = sData[4] + (sData[sDataLen-4] <<8) + (sData[sDataLen-3] <<16) + (sData[sDataLen-2] <<24);

            bool packetIsEncrypted  = frameControl & 0x08;  // bit 3
            bool hasMACField        = frameControl & 0x10;  // bit 4
            bool hasCapabilityField = frameControl & 0x20;  // bit 5
            bool hasDataFields      = frameControl & 0x40;  // bit 6
            
            

            Serial.printf(" -- FrameControl: 0x%04X\n", frameControl);
            if (hasDataFields) {
              Serial.println("    Has data fields");
            }

            if (packetIsEncrypted) {
              Serial.println("    Packet encrypted");
            }

            if (hasCapabilityField) {
              Serial.println("    Has capability field");
            }


            Serial.printf(" -- ProductID:    0x%04X\n", productId);
            Serial.printf(" -- FrameCounter: 0x%02X\n", frameCounter);

            if (hasMACField) {
              Serial.printf(" -- MAC address:  ");
              for (uint8_t i=0; i< 6; i++) {
                Serial.printf("%02X", sData[10-i]);
                if (i != 5) {
                  Serial.print(":");
                }
              }
            }

            Serial.println();

            if (hasCapabilityField) {
              uint8_t  capability   = sData[11];
              Serial.printf(" -- Capability:   0x%02X\n", capability);
            }

            Serial.println();

            if (productId!=  requiredProductId) {
              Serial.printf("Device id mismatch, must be 0x%4X, got: 0x%04X\n", requiredProductId,  productId);
              return;
            }
            advertisedDevice->getScan()->stop(); 
            pServerAddress = new BLEAddress(advertisedDevice->getAddress());
          }
          
      }
    }
};

/**
 * @brief Initializes cihper key data with initial values based on passed encryption key
 * 
 * @param key       Encryption key
 * @param keyLength Encryption key length
 */
void cipherKeyInit(uint8_t *key, uint8_t keyLength ) {
  for (uint16_t i=0; i<CIPHER_KEY_LENGTH; i++ ) {
    cypherKey[i] = i;
  }

  uint16_t j=0, tmp=0;
  for (uint16_t i=0; i<CIPHER_KEY_LENGTH; i++ ) {
    j+= cypherKey[i] + key[i%keyLength];
    j = j & 0xff;
    tmp = cypherKey[i];
    cypherKey[i] = cypherKey[j];
    cypherKey[j] = tmp;
  }
}

/**
 * @brief Get the Mix A data based on reversed MAC and product id, used to initial auth 
  * 
 * @return uint8_t* Pointer to static MixA data
 */
uint8_t* getMixA() {
  static uint8_t authKey[8] = {reversedMac[0], reversedMac[2], reversedMac[5], (uint8_t)(requiredProductId & 0xff), (uint8_t)(requiredProductId & 0xff), reversedMac[4], reversedMac[5], reversedMac[1]};
  return authKey;
}

/**
 * @brief Get the Mix B data based on reversed MAC and product id, used to check incoming notification
 * 
 * @return uint8_t* Pointer to static MixB data
 */

uint8_t* getMixB() {
  static uint8_t authKey[8] = {reversedMac[0], reversedMac[2], reversedMac[5], (uint8_t)((requiredProductId >> 8) & 0xff),  reversedMac[4],  reversedMac[0], reversedMac[5], (uint8_t)(requiredProductId & 0xff)};
  return authKey;
}

/**
 * @brief Initializes cipher with AUTH key
 * 
 */
void authCipherInit() {
  cipherKeyInit(getMixA(), 8);
}

/**
 * @brief Initializes cipher with AUTH CHECK key
 * 
 */
void authCheckCipherInit() {
  cipherKeyInit(getMixB(), 8);
}

/**
 * @brief Initializes cipher with key based on token
 * 
 */
void tokenCipherInit() {
  cipherKeyInit(token, TOKEN_LENGTH);
}

/**
 * @brief Encrypt passed data with prepared key
 * 
 * @param input  Pointer to input plaintext buffer
 * @param output Pointer to output buffer for encrypted data
 * @param length Length of data buffers
 */
void cipherCrypt(uint8_t * input, uint8_t* output,  uint8_t length) {
  uint16_t index1=0, index2=0, tmp=0;
  uint16_t sum;
  uint8_t key[CIPHER_KEY_LENGTH];

  // Copy key, we will modify it
  memcpy(key, cypherKey, CIPHER_KEY_LENGTH);

  for (uint16_t i=0; i<length; i++) {
		index1++;
    index1 = index1 & 0xff;
		
    index2 += key[index1];
    index2 = index2 & 0xff;

    tmp = key[index1];
    key[index1] = key[index2];
    key[index2] = tmp;

		sum =  key[index1] + key[index2];
    sum = sum & 0xff;
		output[i] = input[i] ^ key[sum];
	}
	 
}

void setup() {

  Serial.begin(115200);
  EEPROM.begin(EEPROM_SIZE);
  NimBLEDevice::setPower(ESP_PWR_LVL_P9);

  if (!bForcePair && EEPROM.readULong(0)==0xDEADBEEF) {
    
    uint8_t macBuffer[6];
    EEPROM.readBytes(5, macBuffer, 6);
    EEPROM.readBytes(11, beaconKey, BEACON_KEY_LENGTH);
    pServerAddress = new NimBLEAddress(macBuffer);
    Serial.printf("Have paired device %s\n", pServerAddress->toString().c_str());
    Serial.println("Saved beacon key:");
    HexDump(Serial, beaconKey, BEACON_KEY_LENGTH);
    bPaired = true;
  }

  NimBLEDevice::init("");

  if (pServerAddress == nullptr) {
    Serial.println("Remote control address not defined.");

    pBLEScan = NimBLEDevice::getScan(); //create new scan
    pBLEScan->setAdvertisedDeviceCallbacks(new MyAdvertisedDeviceCallbacks());

    pBLEScan->setActiveScan(true); //active scan uses more power, but get results faster
    pBLEScan->setInterval(100);
    pBLEScan->setWindow(99);  // less or equal setInterval value

    while (!pServerAddress) {
      Serial.print("Scannig for remote, press OFF+M ...\n");
      NimBLEScanResults foundDevices = pBLEScan->start(scanTime, false);
      pBLEScan->clearResults();   // delete results fromBLEScan buffer to release memory
      delay(2000);
    }
    Serial.println("Scan done!");
  }

  Serial.printf("Paired remote control address: %s\n", pServerAddress->toString().c_str()); 

   // Store reversed mac for auth purposes
  memcpy(reversedMac, pServerAddress->getNative(), ESP_BD_ADDR_LEN);
}

// Receive preauth notification and check received token equals
static void onAuthStart(NimBLERemoteCharacteristic* pBLERemoteCharacteristic, 
                                        uint8_t* pData, size_t length, bool isNotify) {
  Serial.println("Auth start notify:");
  // HexDump(Serial, pData, length);

  uint8_t * decrypted1  = (uint8_t *) malloc(length);
  uint8_t * decrypted2  = (uint8_t *) malloc(length);

  // Check response
  authCipherInit();
  cipherCrypt(pData, decrypted1, length);

  authCheckCipherInit();
  cipherCrypt(decrypted1, decrypted2, length);

  Serial.println("Decrypted token");
  HexDump(Serial,decrypted2, length);

  Serial.println("Should be token");
  HexDump(Serial,token, TOKEN_LENGTH);

  free(decrypted1);

  for (size_t i=0; i<TOKEN_LENGTH; i++) {
    if (decrypted2[i]!=token[i]) {
      Serial.println("Tokens are not equal, auth failed");
      free(decrypted2);
      return;
    }
  }

  free(decrypted2);
  bPreAauthDone=true;
}

// Obtain device characteristics
bool ObtainCharacteristics(NimBLEClient* pClient) {
  Serial.println("---- Obtaining chracteristics");

  // Serial.println("--- Services: ");
  // std::vector<NimBLERemoteService*> * pServices =  pClient->getServices(true);

  // for (auto &pService : *pServices) {
  //   Serial.println(pService->toString().c_str());
  // }


  NimBLERemoteService* pXiaomiService = pClient->getService(uuidXiaomiService);
  if (pXiaomiService == nullptr) {
    Serial.print("Failed to find Xiaomi service UUID: ");
    Serial.println(uuidXiaomiService.toString().c_str());
    return false;
  }
  


  // std::vector<NimBLERemoteCharacteristic*>* mChars = pXiaomiService->getCharacteristics(true);
  // Serial.println("Xiaomi service characteristics:");
 
  // for (auto &pCharacteristic : *mChars) {
  //   Serial.println(pCharacteristic->toString().c_str());

  //   std::vector<NimBLERemoteDescriptor*> *mDescriptors = pCharacteristic->getDescriptors();
  //   if (mDescriptors!=nullptr) {
  //     for (auto &desc : *mDescriptors) {
  //       Serial.printf("     Descriptor ");
  //       Serial.println(desc->toString().c_str());
  //     }
  //     Serial.println();
  //   }
  // }

  pXiaomiService->getCharacteristics(true);
  if ((pAuthCharacteristic = pXiaomiService->getCharacteristic(uuidAuthCharacteristic)) == nullptr) {
    Serial.print("Failed to find auth characteristic UUID: ");
    Serial.println(uuidAuthCharacteristic.toString().c_str());
    return false;
  }

  if ((pAuthInitCharacteristic  = pXiaomiService->getCharacteristic(uuidAuthInitCharacteristic)) == nullptr) {
    Serial.print("Failed to find auth init characteristic UUID: ");
    Serial.println(uuidAuthInitCharacteristic.toString().c_str());
    return false;
  }

  if ((pFwVersionCharacteristic = pXiaomiService->getCharacteristic(uuidFwVersionCharacteristic)) == nullptr) {
    Serial.print("Failed to find firmware version characteristic UUID: ");
    Serial.println(uuidFwVersionCharacteristic.toString().c_str());
    return false;
  }

  if ((pBeaconKeyCharacteristic = pXiaomiService->getCharacteristic(uuidBeaconKeyCharacteristic)) == nullptr) {
    Serial.print("Failed to find beacon key characteristic UUID: ");
    Serial.println(uuidBeaconKeyCharacteristic.toString().c_str());
    return false;
  }

  return true;
}

//Connect to the BLE Server that has the name, Service, and Characteristics
bool connectToServer(NimBLEAddress pAddress) {
  NimBLEClient* pClient = nullptr;

  /** Check if we have a client we should reuse first **/
  if(NimBLEDevice::getClientListSize()) {
     pClient = NimBLEDevice::getClientByPeerAddress(pAddress);
     if(pClient) {
        if(!pClient->connect(pAddress, false)) {
          Serial.println("Reconnect failed");
          return false;
        }
        Serial.println("Reconnected client");
     } else {
        pClient = NimBLEDevice::getDisconnectedClient();
     }
  }

    /** No client to reuse? Create a new one. */
  if(!pClient) {
      if(NimBLEDevice::getClientListSize() >= NIMBLE_MAX_CONNECTIONS) {
          Serial.println("Max clients reached - no more connections available");
          return false;
      }

      pClient = NimBLEDevice::createClient();

      Serial.println("New client created");

      //pClient->setClientCallbacks(&clientCB, false);
      /** Set initial connection parameters: These settings are 15ms interval, 0 latency, 120ms timout.
       *  These settings are safe for 3 clients to connect reliably, can go faster if you have less
       *  connections. Timeout should be a multiple of the interval, minimum is 100ms.
       *  Min interval: 12 * 1.25ms = 15, Max interval: 12 * 1.25ms = 15, 0 latency, 51 * 10ms = 510ms timeout
       */
      pClient->setConnectionParams(12,12,0,51);
      /** Set how long we are willing to wait for the connection to complete (seconds), default is 30. */
      pClient->setConnectTimeout(5);


      if (!pClient->connect(pAddress)) {
          /** Created a client but failed to connect, don't need to keep it as it has no data */
          NimBLEDevice::deleteClient(pClient);
          Serial.println("Failed to connect, deleted client");
          return false;
      }
  }

  if(!pClient->isConnected()) {
      if (!pClient->connect(pAddress)) {
          Serial.println("Failed to connect");
          return false;
      }
  }

  Serial.print("Connected to: ");
  Serial.println(pClient->getPeerAddress().toString().c_str());
  Serial.print("RSSI: ");
  Serial.println(pClient->getRssi());

  return ObtainCharacteristics(pClient);
}

/**
 * @brief Extend beacon key (12 bytes) to obtain AES key (16 bytes)
 * 
 */
void prepareAESdata() {
  memcpy(aesKey, beaconKey, 6);
  memcpy(aesKey+10, beaconKey+6, 6);
}
/**
 * @brief Calculate nonce that will be used in encryption process
 * 
 * @param buffer            Nonce buffer pointer
 * @param frameControl      Frame control field from packet
 * @param deviceType        Device type field  from packet
 * @param frameCounter      Frame conter field from packet
 */
void calculateNonce(uint8_t *buffer, uint16_t frameControl, uint16_t deviceType, uint32_t frameCounter) {
  memcpy(buffer, &frameControl, 2);
  memcpy(buffer+2, &deviceType, 2);
  memcpy(buffer+4, &frameCounter, 4);
  memcpy(buffer+8, reversedMac, 5);
}

/**
 * @brief Begins authentication process to pair new device
 * 
 */
void authInit() {
  pAuthInitCharacteristic->writeValue(miAuthStart, 4, false);
    
  // Activate the Notify
  pAuthCharacteristic->subscribe(true, onAuthStart, true);
  pAuthCharacteristic->getDescriptor(uuidAuthDescriptor)->writeValue(notificationOn, 2, true);

  // Initialize cypher with auth key
  authCipherInit();
  
  // Encrypt our token with MixA key
  uint8_t encryptedToken[TOKEN_LENGTH];
  cipherCrypt(token, encryptedToken, TOKEN_LENGTH);

  // Send encrypted token
  pAuthCharacteristic->writeValue(encryptedToken, TOKEN_LENGTH, true);
}

uint32_t lastFrame = 0;


class MyCallbacks: public NimBLEAdvertisedDeviceCallbacks {
    /**
     * @brief Receives BLE advertised packets from remote
     * 
     * @param advertisedDevice 
     */
    
    void onResult(NimBLEAdvertisedDevice *advertisedDevice) {
//      Serial.printf("Advertised Device: %s \n", advertisedDevice->toString().c_str());
      if(advertisedDevice->getAddress().equals(*pServerAddress)) {
        
        
        uint8_t * pPayload    = advertisedDevice->getPayload();
        size_t  szPayloadSize = advertisedDevice->getPayloadLength();
        
        if (szPayloadSize != 25) {
          // Ignore ?!? Maybe status reports
          // Serial.printf("Unexpected payload size, expected=25, got=%d\n", szPayloadSize);
          // HexDump(Serial,(void*) pPayload, szPayloadSize);

          return;
        }
        //       | UUID  | <--- sData --->                                                             | 
        // -- -- | -- -- | -FCE- | -PID- | CNT|    -- MAC --      |   -- payload --   | Counter  | MIC |
        // 18 16 | 95 FE | 58 30 | 53 01 | E2 | 1D 01 ED 41 24 F8 | B3 A7 8D 51 38 9F | 00 00 00 | 87  |
        // 0   1 |  2  3 |  4  5 |  6  7 |  8 |  9 10 11 12 13 14 | 15 16 17 18 19 20 | 21 22 23 | 24  |
   
        uint8_t * sData      = pPayload+4;
        size_t    szDataSize = szPayloadSize-4;

        uint16_t frameControl = (sData[1]<< 8) + sData[0] ;
        uint16_t productId    = (sData[3]<< 8) + sData[2] ;
        uint32_t frameCounter = sData[4] + (sData[szDataSize-4] <<8) + (sData[szDataSize-3] <<16) + (sData[szDataSize-2] <<24);
        
        // TODO: Check MIC?
        // uint8_t  mic          = sData[szDataSize-1];

        uint8_t  *pFields     = sData + 5;
        size_t szFieldsLength = szDataSize - 9;

        // Ignore duplicates
        if (frameCounter == lastFrame) {
          return;
        }

        lastFrame = frameCounter;


        bool packetIsEncrypted  = frameControl & 0x08;  // bit 3
        bool hasMACField        = frameControl & 0x10;  // bit 4
        bool hasCapabilityField = frameControl & 0x20;  // bit 5
        bool hasDataFields      = frameControl & 0x40;  // bit 6

        if (!hasDataFields) {
          Serial.println("Packet does not have data fields, ignore");
          return;
        }
            
        // Serial.printf(" -- FrameControl: 0x%04X\n", frameControl);
        // if (hasDataFields) {
        //   Serial.println("    Has data fields");
        // }

        // if (packetIsEncrypted) {
        //   Serial.println("    Packet encrypted");
        // }

        // if (hasCapabilityField) {
        //   Serial.println("    Has capability field");
        // }


        // Serial.printf(" -- ProductID:    0x%04X\n", productId);
        // Serial.printf(" -- FrameCounter: 0x%02X\n", frameCounter);
        // Serial.printf(" -- MIC:          0x%02X\n", mic);

        // if (hasCapabilityField) {
        //   uint8_t  capability   = sData[11];
        //   Serial.printf(" -- Capability:   0x%02X\n", capability);
        // }
        

        // if (hasMACField) {
        //   Serial.printf(" -- MAC address:  ");
        //   for (uint8_t i=0; i< 6; i++) {
        //     Serial.printf("%02X", sData[10-i]);
        //     if (i != 5) {
        //       Serial.print(":");
        //     }
        //   }
        // }


        // Serial.println();
        if (hasCapabilityField) {
          pFields+= 1;
          szFieldsLength-=1;
        }

        if (hasMACField) {
          pFields+= 6;
          szFieldsLength-=6;
        }

        // Serial.println("Fields:");
        // Serial.printf("[%08X] ", frameCounter);
        // HexDump(Serial,(void*) pFields, szFieldsLength);
        
        if (packetIsEncrypted) {
          uint8_t nonce[NONCE_LENGTH];
          calculateNonce(nonce, frameControl, productId, frameCounter);

          mbedtls_ccm_context ctx;
          mbedtls_ccm_init(&ctx);

          int ret = mbedtls_ccm_setkey(&ctx, MBEDTLS_CIPHER_ID_AES, aesKey, AES_KEY_LENGTH * 8);
          if (ret) {
            Serial.printf("mbedtls_ccm_setkey() failed. Code=%d\n", ret);
            mbedtls_ccm_free(&ctx);
            return;
          }

          uint8_t add = 0x11;
          uint8_t *decryptedFields = (uint8_t*) malloc(szFieldsLength);
          uint8_t tag[4];

          ret = mbedtls_ccm_encrypt_and_tag(&ctx, szFieldsLength, nonce, NONCE_LENGTH, &add, 1, pFields, decryptedFields, tag, 4);
          if (ret) {
             Serial.printf("mbedtls_ccm_auth_encrypt() failed. Code=");
             switch (ret)
            {

            case MBEDTLS_ERR_CCM_BAD_INPUT:
              Serial.println("MBEDTLS_ERR_CCM_BAD_INPUT");
              break;
            
            case MBEDTLS_ERR_CCM_AUTH_FAILED:
              Serial.println("MBEDTLS_ERR_CCM_AUTH_FAILED");
              break;
            
            default:
              Serial.printf("%d", ret);
              break;
            }
            

            mbedtls_ccm_free(&ctx);
            return;
          }

          if (decryptedFields[0] == 1 && decryptedFields[1] ==10 && decryptedFields[1] ==3 ) {
            Serial.println("Unknow payload structure");
            HexDump(Serial, (void *) decryptedFields, szFieldsLength);
          } else {
            if (decryptedFields[5]==2) {
              Serial.printf("HOLD ");
            }

            switch(decryptedFields[3]) {
              case 0x00:
                Serial.println("ON");
                break;
              case 0x01:
                Serial.println("OFF");                
                break;
              case 0x02:
                Serial.println("DAY/NIGHT");                
                break;
              case 0x03:
                Serial.println("+");                
                break;
              case 0x04:
                Serial.println("M");                
                break;
              case 0x05:
                Serial.println("-");                
                break;


                default:
                  Serial.printf("UNKNOWN 0x%02X\n", decryptedFields[3]);
            }
          }

          free(decryptedFields);
          mbedtls_ccm_free(&ctx);
          
        }
      }
          
    }
};

void loop() {

  // Wait for scan process to complete (if any)
  while(pServerAddress == nullptr) { 
    delay(1000);
  }
  // // If not paired, try to authenticate and receive beaconKey
  if (!bPaired) {

    // Try to connect to remote
    while(true) {
      Serial.println("Connecting to remote");
      if (connectToServer(*pServerAddress)) {
        break;
      }

      Serial.println("Cannot connect to remote control, retrying in 5 sec...");
      delay(5000);
      
    }
    Serial.println("Connected to the remote, waiting for auth notification");
    authInit();

  
    while(!bPreAauthDone) { 
      delay(1000); 
    }
    Serial.println("Countinue auth");

    tokenCipherInit();
    uint8_t encryptedConfirm[4];
    cipherCrypt(miAuthConfirm, encryptedConfirm, 4);

    pAuthCharacteristic->writeValue(encryptedConfirm, 4, false);
    Serial.println("Auth done");

    // Turn off auth notifications
    pAuthCharacteristic->getDescriptor(uuidAuthDescriptor)->writeValue(notificationOff, 2, true);

    std::string fw = pFwVersionCharacteristic->readValue();
    uint8_t *fwDecrypted = (uint8_t*) malloc(fw.length());
    cipherCrypt((uint8_t *) fw.data(), fwDecrypted, fw.length());

    Serial.println("FW version:");
    HexDump(Serial, fwDecrypted, fw.length());
    free(fwDecrypted);

    std::string beaconKeyReceived = pBeaconKeyCharacteristic->readValue();
    if (beaconKeyReceived.length() != BEACON_KEY_LENGTH) {
      Serial.printf("Unexpected beacon key length, expected: %d, got: %d\n", BEACON_KEY_LENGTH, beaconKeyReceived.length());
      while(true){ sleep(1000); }; // Maybe restart instead?
    }

    cipherCrypt((uint8_t *) beaconKeyReceived.data(), beaconKey, BEACON_KEY_LENGTH);
    Serial.println("Beacon key:");
    HexDump(Serial, beaconKey, BEACON_KEY_LENGTH);

    // Store paired data to eeprom
    EEPROM.writeULong(0, 0xDEADBEEF);

    // NimBLE address stored in reverse
    const uint8_t * mac = pServerAddress->getNative();
    uint8_t        temp[6];

    std::reverse_copy(mac, mac + ESP_BD_ADDR_LEN, temp);
    EEPROM.writeBytes(5, temp, 6);
    EEPROM.writeBytes(11, beaconKey, BEACON_KEY_LENGTH);

    EEPROM.commit();
  }

  prepareAESdata();
  
  pBLEScan = NimBLEDevice::getScan(); //create new scan
  pBLEScan->setActiveScan(false);
  pBLEScan->setAdvertisedDeviceCallbacks(new MyCallbacks() ,false);

  // Inifinite recieve advertisements
  while(true) { 
    NimBLEScanResults foundDevices = pBLEScan->start(1);
    pBLEScan->clearResults();   // delete results fromBLEScan buffer to release memory
  }
}
