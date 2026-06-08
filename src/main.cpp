// Copyright fukuen. All rights reserved.
// Licensed under the MIT license. See LICENSE file in the project root for full license information.

#include <iostream>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <ctime>
#include <cmath>

#include <mbedtls/md.h>
#include <mbedtls/sha256.h>
#include <M5Unified.h>
#include <WiFi.h>
#include <SD.h>
#include <HTTPClient.h>
#include <WiFiClientSecure.h>
#include <esp_sntp.h>

#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <freertos/semphr.h>

#include "esp_audio_enc_default.h"
#include "esp_audio_enc_reg.h"
#include "esp_aac_enc.h"

#include "utility/led/LED_Strip_Class.hpp"
#include "utility/led/LED_Base.hpp"

#define WIFI_SSID "<WIFI_SSID>"
#define WIFI_PASS "<WIFI_PASS>"

#define ACCESS_KEY "<AWS_ACCESS_KEY>"
#define SECRET_KEY "<AWS_SECRET_KEY>"
#define REGION "<REGION>"
#define BUCKET "<S3_BUCKET>"
#define STORAGE_CLASS "STANDARD"

#define RECORDING_NIGHT_ONLY 0
#define DAY_TIME_HOUR_FROM 6
#define DAY_TIME_HOUR_TO 23

#define FRAME_NUM 8

#define SD_SPI_CS_PIN 4
#define SD_SPI_SCK_PIN 18
#define SD_SPI_MISO_PIN 38
#define SD_SPI_MOSI_PIN 23

static constexpr double OPEN_THRESHOLD = 0.01; // -40db
static constexpr double CLOSE_THRESHOLD = 0.005623413251903491; // -45db
//static constexpr double OPEN_THRESHOLD = 0.007; // -43db
//static constexpr double CLOSE_THRESHOLD = 0.004; // -48db
//static constexpr double OPEN_THRESHOLD = 0.005623413251903491; // -45db
//static constexpr double CLOSE_THRESHOLD = 0.0031622776601683794; // -50db
static constexpr uint32_t SILENCE_STOP_MS = 10000;
static constexpr uint32_t UPLOAD_INTERVAL_MS = 10 * 1000;
static constexpr uint32_t RECORD_SAMPLE_RATE = 16000;
static constexpr size_t LED_COUNT = 10;

WiFiClientSecure client;
HTTPClient http;

static esp_audio_enc_handle_t audio_enc_hd = NULL;
static esp_audio_enc_in_frame_t in_frame = {0};
static esp_audio_enc_out_frame_t out_frame = {0};
static uint8_t *in_frame_buf = NULL;
static uint8_t *out_frame_buf = NULL;
static int in_frame_size = 0;
static int out_frame_size = 0;

static bool active = false;
static bool recording = false;
static uint32_t silence_start_ms = 0;
static uint32_t last_upload_ms = 0;
static double sdUsage = 0.0;

static File file;
static size_t total_sample = 0;
static size_t total_encoded = 0;
static size_t rec_record_idx = 0;

RGBColor colors[10] = {
    {255, 0, 0},
    {0, 255, 0},
    {0, 0, 255},
    {255, 255, 0},
    {0, 255, 255},
    {255, 0, 255},
    {128, 128, 128},
    {255, 128, 0},
    {0, 128, 255},
    {128, 0, 255}
};

const char *rootCACertificate =
    "-----BEGIN CERTIFICATE-----\n"
    "MIIDQTCCAimgAwIBAgITBmyfz5m/jAo54vB4ikPmljZbyjANBgkqhkiG9w0BAQsF\n"
    "ADA5MQswCQYDVQQGEwJVUzEPMA0GA1UEChMGQW1hem9uMRkwFwYDVQQDExBBbWF6\n"
    "b24gUm9vdCBDQSAxMB4XDTE1MDUyNjAwMDAwMFoXDTM4MDExNzAwMDAwMFowOTEL\n"
    "MAkGA1UEBhMCVVMxDzANBgNVBAoTBkFtYXpvbjEZMBcGA1UEAxMQQW1hem9uIFJv\n"
    "b3QgQ0EgMTCCASIwDQYJKoZIhvcNAQEBBQADggEPADCCAQoCggEBALJ4gHHKeNXj\n"
    "ca9HgFB0fW7Y14h29Jlo91ghYPl0hAEvrAIthtOgQ3pOsqTQNroBvo3bSMgHFzZM\n"
    "9O6II8c+6zf1tRn4SWiw3te5djgdYZ6k/oI2peVKVuRF4fn9tBb6dNqcmzU5L/qw\n"
    "IFAGbHrQgLKm+a/sRxmPUDgH3KKHOVj4utWp+UhnMJbulHheb4mjUcAwhmahRWa6\n"
    "VOujw5H5SNz/0egwLX0tdHA114gk957EWW67c4cX8jJGKLhD+rcdqsq08p8kDi1L\n"
    "93FcXmn/6pUCyziKrlA4b9v7LWIbxcceVOF34GfID5yHI9Y/QCB/IIDEgEw+OyQm\n"
    "jgSubJrIqg0CAwEAAaNCMEAwDwYDVR0TAQH/BAUwAwEB/zAOBgNVHQ8BAf8EBAMC\n"
    "AYYwHQYDVR0OBBYEFIQYzIU07LwMlJQuCFmcx7IQTgoIMA0GCSqGSIb3DQEBCwUA\n"
    "A4IBAQCY8jdaQZChGsV2USggNiMOruYou6r4lK5IpDB/G/wkjUu0yKGX9rbxenDI\n"
    "U5PMCCjjmCXPI6T53iHTfIUJrU6adTrCC2qJeHZERxhlbI1Bjjt/msv0tadQ1wUs\n"
    "N+gDS63pYaACbvXy8MWy7Vu33PqUXHeeE6V/Uq2V8viTO96LXFvKWlJbYK8U90vv\n"
    "o/ufQJVtMVT8QtPHRh8jrdkPSHCa2XV4cdFyQzR1bldZwgJcJmApzyMZFo6IQ6XU\n"
    "5MsI+yMRQ+hDKXJioaldXgjUkK642M4UwtBV8ob2xJNDd2ZhwLnoQdeXeGADbkpy\n"
    "rqXRfboQnoZsG4q5WTP468SQvvG5\n"
    "-----END CERTIFICATE-----\n";

String makeTimestampString(const char *format, time_t now, bool useGmTime)
{
  char buf[64] = {};
  struct tm timeinfo;
  if (useGmTime)
  {
    gmtime_r(&now, &timeinfo);
  }
  else
  {
    localtime_r(&now, &timeinfo);
  }
  strftime(buf, sizeof(buf), format, &timeinfo);
  return String(buf);
}

String getAmzDate()
{
  return makeTimestampString("%Y%m%dT%H%M%SZ", time(nullptr), true);
}

String getDateStamp()
{
  return makeTimestampString("%Y%m%d", time(nullptr), true);
}

String makeRecordingFileName()
{
  return "/" + makeTimestampString("%Y%m%d%H%M%S", time(nullptr), false) + ".aac";
}

std::string calculate_hmac_sha256(const std::string &key, const std::string &data)
{
  unsigned char hash[32];
  unsigned int hash_len = sizeof(hash);

  mbedtls_md_context_t ctx;
  mbedtls_md_type_t md_type = MBEDTLS_MD_SHA256;
  mbedtls_md_init(&ctx);
  mbedtls_md_setup(&ctx, mbedtls_md_info_from_type(md_type), 1);
  mbedtls_md_hmac_starts(&ctx, reinterpret_cast<const unsigned char *>(key.c_str()), key.size());
  mbedtls_md_hmac_update(&ctx, reinterpret_cast<const unsigned char *>(data.c_str()), data.size());
  mbedtls_md_hmac_finish(&ctx, hash);
  mbedtls_md_free(&ctx);

  return std::string(reinterpret_cast<char *>(hash), hash_len);
}

String toHexString(const uint8_t *data, size_t len)
{
  std::stringstream ss;
  for (size_t i = 0; i < len; ++i)
  {
    ss << std::hex << std::setw(2) << std::setfill('0') << (int)data[i];
  }
  return String(ss.str().c_str());
}

std::string hmac_to_hex(const std::string &hmac)
{
  std::stringstream ss;
  for (unsigned char c : hmac)
  {
    ss << std::hex << std::setw(2) << std::setfill('0') << (int)c;
  }
  return ss.str();
}

String sha256Hex(const String &str)
{
  unsigned char hash[32];
  mbedtls_sha256_context ctx;
  mbedtls_sha256_init(&ctx);
  mbedtls_sha256_starts(&ctx, 0);
  mbedtls_sha256_update(&ctx, reinterpret_cast<const unsigned char *>(str.c_str()), str.length());
  mbedtls_sha256_finish(&ctx, hash);
  mbedtls_sha256_free(&ctx);
  return toHexString(hash, sizeof(hash));
}

String sha256HexFile(const String &filePath)
{
  unsigned char hash[32];
  char buff[128];

  mbedtls_sha256_context ctx;
  mbedtls_sha256_init(&ctx);
  mbedtls_sha256_starts(&ctx, 0);

  File f = SD.open(filePath, FILE_READ);
  if (!f)
  {
    mbedtls_sha256_free(&ctx);
    return "";
  }

  while (f.available())
  {
    int readSize = f.readBytes(buff, sizeof(buff));
    if (readSize > 0)
    {
      mbedtls_sha256_update(&ctx, reinterpret_cast<const unsigned char *>(buff), readSize);
    }
  }
  f.close();

  mbedtls_sha256_finish(&ctx, hash);
  mbedtls_sha256_free(&ctx);

  return toHexString(hash, sizeof(hash));
}

String detectContentType(const String &path)
{
  String lower = path;
  lower.toLowerCase();

  if (lower.endsWith(".txt")) return "text/plain";
  if (lower.endsWith(".jpg") || lower.endsWith(".jpeg")) return "image/jpeg";
  if (lower.endsWith(".png")) return "image/png";
  if (lower.endsWith(".pdf")) return "application/pdf";
  if (lower.endsWith(".xml")) return "application/xml";
  if (lower.endsWith(".aac")) return "audio/aac";
  return "application/octet-stream";
}

bool isTimestampAacFile(const String &name)
{
  if (!name.endsWith(".aac")) return false;
  if (name.length() != 18) return false;

  for (int i = 0; i < 14; ++i)
  {
    if (!isDigit(name[i])) return false;
  }
  return true;
}

void calcSdUsage()
{
  uint64_t cardSize = SD.cardSize();
  uint64_t usedBytes = SD.usedBytes();
  sdUsage = usedBytes / cardSize;
}

void printDirectory(File dir, int numTabs)
{
  char timeStr[32];
  while (true)
  {
    File entry = dir.openNextFile();
    if (!entry)
    {
      dir.rewindDirectory();
      break;
    }

    for (uint8_t i = 0; i < numTabs; i++)
    {
      Serial.print('\t');
    }

    Serial.print(entry.name());
    Serial.print('\t');
    Serial.print(entry.size());
    Serial.print('\t');

    time_t last = entry.getLastWrite();
    strftime(timeStr, sizeof(timeStr), "%Y/%m/%d %H:%M:%S", localtime(&last));
    Serial.print(timeStr);

    if (entry.isDirectory())
    {
      Serial.println("/");
      printDirectory(entry, numTabs + 1);
    }
    else
    {
      Serial.println();
    }
    entry.close();
  }
}

void removeZeroByteAacFiles()
{
  File dir = SD.open("/");
  if (!dir) return;

  while (true)
  {
    File entry = dir.openNextFile();
    if (!entry)
    {
      dir.rewindDirectory();
      break;
    }

    if (!entry.isDirectory())
    {
      String name = String(entry.name());
      if (isTimestampAacFile(name) && entry.size() == 0)
      {
        String path = "/" + name;
        Serial.printf("\nremove zero byte file: %s", path.c_str());
        entry.close();
        SD.remove(path);
        continue;
      }
    }
    entry.close();
  }
  dir.close();
}

String findOldestAacFile()
{
  File dir = SD.open("/");
  if (!dir) return "";

  String oldest = "";
  while (true)
  {
    File entry = dir.openNextFile();
    if (!entry)
    {
      dir.rewindDirectory();
      break;
    }

    if (!entry.isDirectory())
    {
      String name = String(entry.name());
      if (isTimestampAacFile(name))
      {
        if (oldest.isEmpty() || name < oldest)
        {
          oldest = name;
        }
      }
    }
    entry.close();
  }
  dir.close();
  return oldest;
}

bool isDaytime()
{
  struct tm timeInfo;
  if (getLocalTime(&timeInfo))
  {
    return (timeInfo.tm_hour >= DAY_TIME_HOUR_FROM) && (timeInfo.tm_hour < DAY_TIME_HOUR_TO);
  }
  return false;
}

double calcRms(const int16_t *data, size_t sampleCount)
{
  if (sampleCount == 0) return 0.0;

  double sumSquares = 0.0;
  for (size_t i = 0; i < sampleCount; ++i)
  {
    double normalized = data[i] / 32768.0;
    sumSquares += normalized * normalized;
  }

  return sqrt(sumSquares / sampleCount);
}

void clearLed()
{
  RGBColor *buf = M5.Led.getBuffer();
  for (size_t i = 0; i < LED_COUNT; ++i)
  {
    buf[i] = {0};
  }

  M5.Led.setColors(buf, 0, LED_COUNT);
}

void showLevelMeter(double level)
{
  RGBColor *buf = M5.Led.getBuffer();
  clearLed();

  if (level > CLOSE_THRESHOLD) buf[0] = colors[1];
  if (level > 0.01)            buf[1] = colors[1];
  if (level > 0.1)             buf[2] = colors[1];
  if (level > 0.2)             buf[3] = colors[3];
  if (level > 0.3)             buf[4] = colors[0];

  M5.Led.setColors(buf, 0, LED_COUNT);
}

void showActiveMeter(bool isActive)
{
  RGBColor *buf = M5.Led.getBuffer();
  for (size_t i = 0; i < LED_COUNT; ++i)
  {
    buf[i] = {0};
  }
  if (isActive) buf[5] = RGBColor(0, 0, 16);
  if (sdUsage > 0.8) buf[2] = RGBColor(16, 8 ,0);

  M5.Led.setColors(buf, 0, LED_COUNT);
}

void initAacEncoder()
{
  esp_audio_err_t ret = esp_audio_enc_register_default();
  if (ret != ESP_AUDIO_ERR_OK)
  {
    Serial.printf("audio encoder register error: %d\n", ret);
    return;
  }

  esp_aac_enc_config_t aac_cfg = ESP_AAC_ENC_CONFIG_DEFAULT();
  aac_cfg.sample_rate = 16000;
  aac_cfg.channel = 1;
  aac_cfg.bitrate = 22050;
  aac_cfg.adts_used = true;

  esp_audio_enc_config_t enc_cfg = {
      .type = ESP_AUDIO_TYPE_AAC,
      .cfg = &aac_cfg,
      .cfg_sz = sizeof(aac_cfg)};

  ret = esp_audio_enc_open(&enc_cfg, &audio_enc_hd);
  if (ret != ESP_AUDIO_ERR_OK)
  {
    Serial.printf("audio encoder open error: %d\n", ret);
    return;
  }

  ret = esp_audio_enc_get_frame_size(audio_enc_hd, &in_frame_size, &out_frame_size);
  if (ret != ESP_AUDIO_ERR_OK)
  {
    Serial.printf("audio encoder get frame size error: %d\n", ret);
    return;
  }

  in_frame_buf = static_cast<uint8_t *>(malloc(static_cast<size_t>(in_frame_size) * FRAME_NUM));
  out_frame_buf = static_cast<uint8_t *>(malloc(static_cast<size_t>(out_frame_size)));

  if (!in_frame_buf || !out_frame_buf)
  {
    Serial.println("failed to allocate encoder buffers");
    return;
  }

  in_frame.buffer = in_frame_buf;
  in_frame.len = static_cast<size_t>(in_frame_size);

  out_frame.buffer = out_frame_buf;
  out_frame.len = static_cast<size_t>(out_frame_size);
  memset(out_frame_buf, 0 , out_frame.len);

  Serial.printf("\nAAC encoder initialized. in=%d, out=%d\n", in_frame_size, out_frame_size);
}

void closeAacEncoder()
{
  if (audio_enc_hd)
  {
    esp_audio_enc_close(audio_enc_hd);
    audio_enc_hd = NULL;
  }

  esp_audio_enc_unregister_default();

  if (in_frame_buf)
  {
    free(in_frame_buf);
    in_frame_buf = NULL;
  }

  if (out_frame_buf)
  {
    free(out_frame_buf);
    out_frame_buf = NULL;
  }
}

bool encodeCurrentFrame()
{
  esp_audio_err_t ret = esp_audio_enc_process(audio_enc_hd, &in_frame, &out_frame);
  if (ret != ESP_AUDIO_ERR_OK)
  {
    Serial.printf("\nFail to encode data ret: %d", ret);
    return false;
  }
  return true;
}

bool encodeOldestFrame()
{
  // example curr:0, next:1, oldest: 2
  // example curr:7, next:0, oldest: 1
  int oldest_record_idx = rec_record_idx + 2;
  if (oldest_record_idx >= FRAME_NUM)
  {
    oldest_record_idx -= FRAME_NUM;
  }
  in_frame.buffer = in_frame_buf + (oldest_record_idx * in_frame_size);
  return encodeCurrentFrame();
}

void updateSoundActivity(const int16_t *buffer, size_t sampleCount)
{
  uint32_t now_ms = millis();
  double r = calcRms(buffer, sampleCount);

  if (active)
  {
    if (r > CLOSE_THRESHOLD)
    {
      silence_start_ms = 0;
    }
    else
    {
      if (silence_start_ms == 0)
      {
        silence_start_ms = now_ms;
      }
      else if ((now_ms - silence_start_ms) >= SILENCE_STOP_MS)
      {
        active = false;
        silence_start_ms = 0;
      }
    }
  }
  else
  {
    if (r > OPEN_THRESHOLD)
    {
      active = true;
      silence_start_ms = 0;
    }
  }

  if (RECORDING_NIGHT_ONLY && isDaytime())
  {
    active = false;
  }
  if (sdUsage > 0.8)
  {
    active = false;
  }
}

bool startRecording()
{
  calcSdUsage();
  if (recording) return true;

  String path = makeRecordingFileName();
  file = SD.open(path, FILE_WRITE, true);
  if (!file)
  {
    Serial.printf("\nfailed to open recording file: %s", path.c_str());
    return false;
  }

  total_sample = 0;
  total_encoded = 0;
  recording = true;

  Serial.printf("\nRecording start: %s", path.c_str());
  return true;
}

bool appendRecordingFrame()
{
  if (!recording || !file) return false;

  if (!encodeOldestFrame())
  {
    return false;
  }

  size_t written = file.write(reinterpret_cast<uint8_t *>(out_frame.buffer), out_frame.encoded_bytes);
  if (written != out_frame.encoded_bytes)
  {
    Serial.printf("\nfile write error. expected=%u actual=%u", out_frame.encoded_bytes, written);
    return false;
  }

  total_sample += in_frame_size;
  total_encoded += out_frame.encoded_bytes;
  return true;
}

void stopRecording()
{
  if (!recording) return;

  if (file)
  {
    file.close();
  }

  Serial.printf("\n samples: %u", total_sample);
  Serial.printf("\n encoded: %u", total_encoded);
  Serial.printf("\nRecording end.");

  recording = false;
  calcSdUsage();
  // wait 10s for next upload
  last_upload_ms = time(nullptr);
}

String buildCanonicalHeaders(const String &host, const String &payloadHash, const String &amzDate)
{
  String headers;
  headers += "host:" + host + "\n";
  headers += "x-amz-content-sha256:" + payloadHash + "\n";
  headers += "x-amz-date:" + amzDate + "\n";
  headers += "x-amz-storage-class:STANDARD\n";
  return headers;
}

bool uploadFileToS3(
    const String &accessKey,
    const String &secretKey,
    const String &region,
    const String &bucket,
    const String &filePath,
    const String &objectKey)
{
  String amzDate = getAmzDate();
  String dateStamp = getDateStamp();

  String host = bucket + ".s3." + region + ".amazonaws.com";
  String endpoint = "https://" + host + "/" + objectKey;

  Serial.print("\ncalculating file sha256...");
  String payloadHash = sha256HexFile(filePath);
  if (payloadHash.isEmpty())
  {
    Serial.println(" failed");
    return false;
  }
  Serial.println(" ok");

  String canonicalUri = "/" + objectKey;
  String canonicalHeaders = buildCanonicalHeaders(host, payloadHash, amzDate);
  String signedHeaders = "host;x-amz-content-sha256;x-amz-date;x-amz-storage-class";

  String canonicalRequest =
      "PUT\n" +
      canonicalUri + "\n\n" +
      canonicalHeaders + "\n" +
      signedHeaders + "\n" +
      payloadHash;

  String algorithm = "AWS4-HMAC-SHA256";
  String credentialScope = dateStamp + "/" + region + "/s3/aws4_request";
  String stringToSign =
      algorithm + "\n" +
      amzDate + "\n" +
      credentialScope + "\n" +
      sha256Hex(canonicalRequest);

  std::string kDate = calculate_hmac_sha256("AWS4" + std::string(secretKey.c_str()), std::string(dateStamp.c_str()));
  std::string kRegion = calculate_hmac_sha256(kDate, std::string(region.c_str()));
  std::string kService = calculate_hmac_sha256(kRegion, "s3");
  std::string kSigning = calculate_hmac_sha256(kService, "aws4_request");
  std::string signature = hmac_to_hex(calculate_hmac_sha256(kSigning, std::string(stringToSign.c_str())));

  String authorization =
      algorithm + " Credential=" + accessKey + "/" + credentialScope +
      ", SignedHeaders=" + signedHeaders +
      ", Signature=" + String(signature.c_str());

  client.setCACert(rootCACertificate);

  File uploadFile = SD.open(filePath, FILE_READ);
  if (!uploadFile)
  {
    Serial.printf("\nfailed to open upload file: %s", filePath.c_str());
    return false;
  }

  http.begin(client, endpoint.c_str());
  http.addHeader("Authorization", authorization);
  http.addHeader("x-amz-date", amzDate);
  http.addHeader("x-amz-storage-class", STORAGE_CLASS);
  http.addHeader("x-amz-content-sha256", payloadHash);
  http.addHeader("Content-Type", detectContentType(filePath));

  int contentSize = uploadFile.size();
  int httpResponseCode = http.sendRequest("PUT", &uploadFile, contentSize);
  uploadFile.close();

  if (httpResponseCode > 0)
  {
    Serial.printf("\nS3 response: %d\n", httpResponseCode);
    Serial.println(http.getString());
  }
  else
  {
    Serial.printf("\nHTTP request failed: %d\n", httpResponseCode);
  }

  http.end();
  return httpResponseCode == 200;
}

bool shouldTryUpload()
{
  if (recording) return false;
  if (WiFi.status() != WL_CONNECTED) return false;

  uint32_t now_ms = millis();
  if ((now_ms - last_upload_ms) < UPLOAD_INTERVAL_MS)
  {
    return false;
  }

  last_upload_ms = now_ms;
  return true;
}

void tryUploadOneFile()
{
  if (!shouldTryUpload())
  {
    return;
  }

  removeZeroByteAacFiles();

  String fileName = findOldestAacFile();
  if (fileName.isEmpty())
  {
    return;
  }

  String filePath = "/" + fileName;
  String objectKey = fileName.substring(0, 8) + "/" + fileName;

  Serial.printf("\nupload target: %s -> %s", filePath.c_str(), objectKey.c_str());

  bool ok = uploadFileToS3(ACCESS_KEY, SECRET_KEY, REGION, BUCKET, filePath, objectKey);
  if (ok)
  {
    Serial.print("\nFile upload to s3 success.");
    SD.remove(filePath);
    Serial.print("\nUploaded file removed: " + fileName);
  }
  else
  {
    Serial.print("\nFile upload to s3 failed.");
  }
  calcSdUsage();
}

void processAudioFrame()
{
  size_t sampleCount = in_frame_size / 2;
  updateSoundActivity(reinterpret_cast<int16_t *>(in_frame.buffer), sampleCount);

  if (active)
  {
    if (!recording)
    {
      if (!startRecording())
      {
        return;
      }
    }
    appendRecordingFrame();
  }
  else
  {
    if (recording)
    {
      stopRecording();
    }
    else
    {
      tryUploadOneFile();
      delay(10);
    }
  }
}

void startNextMicRecord()
{
  int next_record_idx = rec_record_idx + 1;
  if (next_record_idx >= FRAME_NUM)
  {
    next_record_idx = 0;
  }
  M5.Mic.record(reinterpret_cast<int16_t *>(in_frame_buf + next_record_idx * in_frame_size), in_frame_size / 2, RECORD_SAMPLE_RATE, false);
}

void selectCurrentInputFrame()
{
  in_frame.buffer = in_frame_buf + (rec_record_idx * in_frame_size);
  rec_record_idx += 1;
  if (rec_record_idx >= FRAME_NUM)
  {
    rec_record_idx = 0;
  }
}

void waitMicRecordingComplete()
{
  while (M5.Mic.isRecording())
  {
    delay(1);
  }
}

void syncClock()
{
  while (WiFi.status() != WL_CONNECTED) {
    Serial.print('.');
    delay(1000);
  }

  configTime(9 * 3600, 0, "ntp.nict.jp", "pool.ntp.org", "time.nist.gov");

  Serial.print("\nNTP sync");
  while (sntp_get_sync_status() != SNTP_SYNC_STATUS_COMPLETED) {
    Serial.print('.');
    delay(1000);
  }

  time_t t = time(nullptr) + 1;  // Advance one second.
  while (t > time(nullptr));     // Synchronization in seconds
  M5.Rtc.setDateTime(gmtime(&t));

  Serial.print("\nTime synced.");
  Serial.println("\nNow: " + makeTimestampString("%Y/%m/%d %H:%M:%S+09:00", time(nullptr), false));
}

void wifiEvent(WiFiEvent_t event) {
  switch (event) {
    case ARDUINO_EVENT_WIFI_STA_GOT_IP:
      syncClock();
      break;
    default:
      break;
  }
}
void initWiFi()
{
  WiFi.begin(WIFI_SSID, WIFI_PASS);
  Serial.print("\nConnecting to WiFi");

  syncClock();
}

void showSdCardInfo()
{
  File root = SD.open("/");
  printDirectory(root, 0);
  root.close();

  calcSdUsage();
  Serial.printf("\nSD usage: %.2lf%%", sdUsage * 100);
}

bool initSdCard()
{
  SPI.begin(SD_SPI_SCK_PIN, SD_SPI_MISO_PIN, SD_SPI_MOSI_PIN, SD_SPI_CS_PIN);
  if (!SD.begin(SD_SPI_CS_PIN, SPI, 25000000))
  {
    Serial.print("\nSD card not detected\n");
    return false;
  }

  Serial.print("\nSD card detected\n");

  showSdCardInfo();
  return true;
}

void initLed()
{
  auto busled = std::make_shared<m5::LedBus_RMT>();
  auto buscfg = busled->getConfig();
  buscfg.pin_data = 25;
  busled->setConfig(buscfg);

  auto led_strip = std::make_shared<m5::LED_Strip_Class>();
  auto ledcfg = led_strip->getConfig();
  ledcfg.led_count = LED_COUNT;
  ledcfg.byte_per_led = 3;
  ledcfg.color_order = m5::LED_Strip_Class::config_t::color_order_grb;
  led_strip->setConfig(ledcfg);

  led_strip->setBus(busled);
  M5.Led.setLedInstance(led_strip);
  M5.Led.begin();

  clearLed();
}

void initMic()
{
  M5.Speaker.setVolume(0);
  M5.Speaker.end();
  M5.Mic.begin();
}

void startInitialMicRecord()
{
  rec_record_idx = FRAME_NUM - 1;
  for (int i = 0; i < FRAME_NUM; i++)
  {
    waitMicRecordingComplete();
    startNextMicRecord();
  }
  memset(in_frame_buf, 0 , FRAME_NUM * in_frame_size);
}

void setup()
{
  auto cfg = M5.config();
  M5.begin(cfg);
  Serial.begin(115200);

  initWiFi();

  if (!initSdCard())
  {
    while (1) { delay(1000); }
  }

  initMic();
  initAacEncoder();
  initLed();

  startInitialMicRecord();

  // skip top noise
  selectCurrentInputFrame();
  encodeOldestFrame();

  Serial.print("\nProgram started.");
}

void loop()
{
  waitMicRecordingComplete();
  startNextMicRecord();
  selectCurrentInputFrame();
  processAudioFrame();

  M5.update();
  delay(1);
}
