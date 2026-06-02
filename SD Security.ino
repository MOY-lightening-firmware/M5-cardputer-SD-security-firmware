// ========================
// SD SECURITY FIRMWARE V8.3
// WiFi Security Scanner
// M5Cardputer Edition
// ========================

#include <M5Cardputer.h>
#include <WiFi.h>
#include <vector>
#include <map>
#include "esp_wifi.h"
#include "esp_wifi_types.h"
#include "esp_system.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/queue.h"


#define COLOR_BG      0x0000
#define COLOR_TEXT    0x07E0
#define COLOR_WARN    0xFBE0
#define COLOR_DANGER  0xF800
#define COLOR_SAFE    0x07E0
#define COLOR_HEADER  0x001F
#define COLOR_WHITE   0xFFFF
#define COLOR_CYAN    0x07FF
#define COLOR_GRAY    0x4208
#define COLOR_PURPLE  0xF81F
#define COLOR_ORANGE  0xFC60


struct WiFiNetwork {
    String  ssid;
    int32_t rssi;
    uint8_t encType;
    uint8_t bssid[6];
    int32_t channel;
};

struct TestResult {
    String name;
    String detail;
    int    severity;
    int    score;
};

struct AttackEvent {
    String   type;
    String   detail;
    uint32_t timestamp;
    uint8_t  bssid[6];
    uint32_t count;
    String   targetSSID;
};

typedef struct {
    uint16_t frame_ctrl;
    uint16_t duration;
    uint8_t  addr1[6];
    uint8_t  addr2[6];
    uint8_t  addr3[6];
    uint16_t seq_ctrl;
} __attribute__((packed)) wifi_mgmt_hdr_t;

struct AttackInfo {
    uint8_t  attackerMAC[6];
    uint8_t  victimMAC[6];
    uint8_t  apBSSID[6];
    uint8_t  channel;
    uint8_t  subtype;
    uint32_t timestamp;
    uint16_t reason;
};


#define DEAUTH_WINDOW_MS   1000
#define DEAUTH_THRESHOLD   2
#define ATTACK_CLEAR_MS    8000
#define ISR_QUEUE_SIZE     64
#define ATTACKER_TRACK_MAX 20


static std::vector<WiFiNetwork> allNets;
static std::vector<WiFiNetwork> targetAPs;
static std::vector<TestResult>  results;

static AttackEvent lastEvent;
static bool        hasEvent = false;

static String  selectedSSID = "";
static int     selIdx       = 0;
static int     listScroll   = 0;
static int     repScroll    = 0;
static int     menuState    = 0;

static unsigned long lastKeyTime    = 0;
static unsigned long lastScanTime   = 0;
static unsigned long lastBlinkTime  = 0;
static unsigned long lastMonUpdate  = 0;
static unsigned long lastScrollTime = 0;
static unsigned long windowStartMs  = 0;
static unsigned long lastAttackMs   = 0;
static unsigned long lastETCheck    = 0;

static int  scrollPos = 0;
static bool scrollFwd = true;
#define SCROLL_SPEED 200

static int  testStep      = 0;
static bool testRunning   = false;
static unsigned long testTimer = 0;
static int  totalScore    = 100;
static bool firstTestDraw = true;
static int  lastDrawnStep = -1;

static bool     attackDetected   = false;
static bool     blinkState       = false;
static int      monitorChannel   = 1;
static int      deauthCount      = 0;
static int      disassocCount    = 0;
static int      evilTwinCount    = 0;
static int      packetsPerSecond = 0;

struct AttackerRecord {
    uint8_t  mac[6];
    uint32_t firstSeen;
    uint32_t lastSeen;
    uint32_t packetCount;
    uint8_t  targetChannel;
    bool     active;
    uint8_t  apBSSID[6];
    String   apSSID;
};
static AttackerRecord attackerTable[ATTACKER_TRACK_MAX];
static int attackerCount = 0;

static QueueHandle_t attackQueue    = nullptr;
static volatile bool promiscRunning = false;

static volatile uint32_t rawDeauthCount   = 0;
static volatile uint32_t rawDisassocCount = 0;
static volatile uint32_t totalMgmtCount   = 0;
static volatile uint32_t totalDataCount   = 0;


bool keyIn(std::vector<char>& w, char c) {
    char u = (c>='a'&&c<='z') ? c-32 : c;
    char l = (c>='A'&&c<='Z') ? c+32 : c;
    for(char ch : w) if(ch==c||ch==u||ch==l) return true;
    return false;
}

bool keyInExact(std::vector<char>& w, char c) {
    for(char ch : w) if(ch==c) return true;
    return false;
}

String bssidStr(const uint8_t* b) {
    char buf[18];
    sprintf(buf,"%02X:%02X:%02X:%02X:%02X:%02X",
            b[0],b[1],b[2],b[3],b[4],b[5]);
    return String(buf);
}

String bssidShort(const uint8_t* b) {
    char buf[10];
    sprintf(buf,"%02X:%02X:%02X",b[3],b[4],b[5]);
    return String(buf);
}

String encStr(uint8_t e) {
    switch(e) {
        case WIFI_AUTH_OPEN:            return "OPEN";
        case WIFI_AUTH_WEP:             return "WEP ";
        case WIFI_AUTH_WPA_PSK:         return "WPA ";
        case WIFI_AUTH_WPA2_PSK:        return "WPA2";
        case WIFI_AUTH_WPA_WPA2_PSK:    return "WP12";
        case WIFI_AUTH_WPA2_ENTERPRISE: return "ENT ";
        case WIFI_AUTH_WPA3_PSK:        return "WPA3";
        default:                         return "????";
    }
}

String clip(String s, int mx) {
    if((int)s.length() > mx) return s.substring(0,mx-1)+"~";
    return s;
}

String padR(String s, int len) {
    while((int)s.length() < len) s += " ";
    if((int)s.length() > len) s = s.substring(0,len);
    return s;
}

bool bssidExists(const uint8_t* b) {
    for(auto& n : allNets)
        if(memcmp(n.bssid,b,6)==0) return true;
    return false;
}

bool macIsZero(const uint8_t* m) {
    for(int i=0;i<6;i++) if(m[i]!=0) return false;
    return true;
}

String findSSIDforBSSID(const uint8_t* bssid) {
    for(auto& n : allNets)
        if(memcmp(n.bssid,bssid,6)==0) return n.ssid;
    return "";
}


void setLastEvent(String type, String detail,
                  const uint8_t* bssid,
                  uint32_t cnt=1,
                  String tSSID="") {
    if(hasEvent &&
       lastEvent.type==type &&
       lastEvent.detail==detail) {
        lastEvent.count    += cnt;
        lastEvent.timestamp = millis()/1000;
        return;
    }
    lastEvent.type      = type;
    lastEvent.detail    = clip(detail, 22);
    lastEvent.timestamp = millis()/1000;
    lastEvent.count     = cnt;
    lastEvent.targetSSID= tSSID;
    if(bssid) memcpy(lastEvent.bssid, bssid, 6);
    else       memset(lastEvent.bssid, 0, 6);
    hasEvent = true;
}


AttackerRecord* trackAttacker(const uint8_t* mac,
                               uint8_t ch,
                               const uint8_t* apBSSID=nullptr) {
    for(int i=0;i<attackerCount;i++) {
        if(memcmp(attackerTable[i].mac,mac,6)==0) {
            attackerTable[i].lastSeen      = millis();
            attackerTable[i].packetCount++;
            attackerTable[i].targetChannel = ch;
            attackerTable[i].active        = true;
            if(apBSSID) {
                memcpy(attackerTable[i].apBSSID,apBSSID,6);
                if(attackerTable[i].apSSID.isEmpty())
                    attackerTable[i].apSSID=findSSIDforBSSID(apBSSID);
            }
            return &attackerTable[i];
        }
    }
    int slot=0;
    if(attackerCount<ATTACKER_TRACK_MAX) {
        slot=attackerCount++;
    } else {
        int oldest=0;
        for(int i=1;i<ATTACKER_TRACK_MAX;i++)
            if(attackerTable[i].lastSeen<attackerTable[oldest].lastSeen)
                oldest=i;
        slot=oldest;
    }
    auto& r=attackerTable[slot];
    memcpy(r.mac,mac,6);
    r.firstSeen     =millis();
    r.lastSeen      =millis();
    r.packetCount   =1;
    r.targetChannel =ch;
    r.active        =true;
    if(apBSSID) {
        memcpy(r.apBSSID,apBSSID,6);
        r.apSSID=findSSIDforBSSID(apBSSID);
    } else {
        memset(r.apBSSID,0,6);
        r.apSSID="";
    }
    return &r;
}


void IRAM_ATTR promiscuousCallback(
    void* buf, wifi_promiscuous_pkt_type_t type)
{
    wifi_promiscuous_pkt_t* pkt=(wifi_promiscuous_pkt_t*)buf;
    uint16_t len=pkt->rx_ctrl.sig_len;

    if(type==WIFI_PKT_MGMT) {
        if(len<24) return;
        wifi_mgmt_hdr_t* hdr=(wifi_mgmt_hdr_t*)pkt->payload;
        uint8_t ftype   =(hdr->frame_ctrl&0x000C)>>2;
        uint8_t fsubtype=(hdr->frame_ctrl&0x00F0)>>4;
        if(ftype!=0) return;
        totalMgmtCount++;
        if(fsubtype==12||fsubtype==10) {
            if(fsubtype==12) rawDeauthCount++;
            else             rawDisassocCount++;
            if(len>=26) {
                AttackInfo info;
                memcpy(info.attackerMAC,hdr->addr2,6);
                memcpy(info.victimMAC,  hdr->addr1,6);
                memcpy(info.apBSSID,    hdr->addr3,6);
                info.channel  =(uint8_t)pkt->rx_ctrl.channel;
                info.subtype  =fsubtype;
                info.timestamp=millis();
                info.reason   =(len>=28)?
                    (pkt->payload[24]|(pkt->payload[25]<<8)):0;
                if(attackQueue) {
                    BaseType_t hp=pdFALSE;
                    xQueueSendFromISR(attackQueue,&info,&hp);
                }
            }
        }
    } else if(type==WIFI_PKT_DATA) {
        totalDataCount++;
    }
}


void startPromiscuous(uint8_t channel=0) {
    if(promiscRunning) return;
    if(channel==0) channel=monitorChannel;
    wifi_promiscuous_filter_t f;
    f.filter_mask=WIFI_PROMIS_FILTER_MASK_MGMT|
                  WIFI_PROMIS_FILTER_MASK_DATA;
    esp_wifi_set_promiscuous_filter(&f);
    esp_wifi_set_promiscuous_rx_cb(&promiscuousCallback);
    esp_wifi_set_channel(channel,WIFI_SECOND_CHAN_NONE);
    esp_wifi_set_promiscuous(true);
    promiscRunning=true;
}

void stopPromiscuous() {
    if(!promiscRunning) return;
    esp_wifi_set_promiscuous(false);
    promiscRunning=false;
    vTaskDelay(pdMS_TO_TICKS(10));
}


void updateMonitor() {
    unsigned long now=millis();
    if(now-lastMonUpdate<200) return;
    lastMonUpdate=now;

    AttackInfo info;
    while(attackQueue &&
          xQueueReceive(attackQueue,&info,0)==pdTRUE) {
        if(!macIsZero(info.attackerMAC))
            trackAttacker(info.attackerMAC,
                          info.channel,
                          info.apBSSID);
    }

    if(now-windowStartMs>=(unsigned long)DEAUTH_WINDOW_MS) {
        uint32_t dCnt=rawDeauthCount;
        uint32_t aCnt=rawDisassocCount;
        rawDeauthCount  =0;
        rawDisassocCount=0;
        windowStartMs   =now;
        packetsPerSecond=(int)(dCnt+aCnt);

        uint32_t total=dCnt+aCnt;
        if(total>=(uint32_t)DEAUTH_THRESHOLD) {
            attackDetected=true;
            lastAttackMs  =now;
            deauthCount  +=(int)dCnt;
            disassocCount+=(int)aCnt;

            uint8_t  topAtk[6]={0};
            String   topSSID  ="";
            uint32_t maxPkt   =0;
            for(int i=0;i<attackerCount;i++) {
                auto& a=attackerTable[i];
                if(a.active&&(now-a.lastSeen)<3000&&
                   a.packetCount>maxPkt) {
                    maxPkt=a.packetCount;
                    memcpy(topAtk,a.mac,6);
                    topSSID=a.apSSID;
                }
            }
            String sev=(total>=20)?"HEAVY":
                       (total>=8) ?"MED":"LIGHT";
            String det=sev+":"+String(total)+"p/s";
            if(!macIsZero(topAtk))
                det+=" "+bssidShort(topAtk);
            if(!topSSID.isEmpty())
                det+=">"+topSSID.substring(0,6);

            setLastEvent(
                dCnt>0?"DEAUTH":"DISASSOC",
                det,
                macIsZero(topAtk)?nullptr:topAtk,
                total, topSSID);
        }
    }

    for(int i=0;i<attackerCount;i++)
        if(attackerTable[i].active&&
           (now-attackerTable[i].lastSeen)>12000)
            attackerTable[i].active=false;

    if(attackDetected&&lastAttackMs>0)
        if(now-lastAttackMs>=(unsigned long)ATTACK_CLEAR_MS)
            attackDetected=false;

    if(now-lastETCheck>60000) {
        lastETCheck=now;
        bool was=promiscRunning;
        if(was){esp_wifi_set_promiscuous(false);promiscRunning=false;}
        vTaskDelay(pdMS_TO_TICKS(30));
        int n=WiFi.scanNetworks(false,true,false,300);
        if(n>0) {
            for(int i=0;i<n;i++) {
                if(WiFi.SSID(i)==selectedSSID) {
                    bool known=false;
                    for(auto& ap:targetAPs)
                        if(memcmp(ap.bssid,WiFi.BSSID(i),6)==0)
                        {known=true;break;}
                    if(!known) {
                        uint8_t fakeMAC[6];
                        memcpy(fakeMAC,WiFi.BSSID(i),6);
                        evilTwinCount++;
                        attackDetected=true;
                        lastAttackMs  =now;
                        String det="MAC:"+bssidShort(fakeMAC)+
                                   " CH"+String(WiFi.channel(i));
                        setLastEvent("EVIL TWIN",det,
                                     fakeMAC,1,selectedSSID);
                    }
                }
            }
            WiFi.scanDelete();
        }
        vTaskDelay(pdMS_TO_TICKS(20));
        if(was){
            esp_wifi_set_channel(monitorChannel,WIFI_SECOND_CHAN_NONE);
            esp_wifi_set_promiscuous(true);
            promiscRunning=true;
        }
    }
}


void startMonitor() {
    stopPromiscuous();
    if(attackQueue){vQueueDelete(attackQueue);attackQueue=nullptr;}

    rawDeauthCount  =0; rawDisassocCount=0;
    totalMgmtCount  =0; totalDataCount  =0;
    attackDetected  =false;
    deauthCount     =0; disassocCount=0; evilTwinCount=0;
    hasEvent        =false;
    packetsPerSecond=0;
    lastAttackMs    =0;
    windowStartMs   =millis();
    lastETCheck     =millis()-55000;
    attackerCount   =0;
    memset(attackerTable,0,sizeof(attackerTable));

    monitorChannel=1;
    for(auto& ap:targetAPs){monitorChannel=ap.channel;break;}

    attackQueue=xQueueCreate(ISR_QUEUE_SIZE,sizeof(AttackInfo));
    WiFi.mode(WIFI_STA);
    WiFi.disconnect();
    vTaskDelay(pdMS_TO_TICKS(150));
    esp_wifi_set_max_tx_power(84);
    startPromiscuous(monitorChannel);

    setLastEvent("SYSTEM","Monitor started CH:"+
                 String(monitorChannel),nullptr,1,selectedSSID);

    menuState    =5;
    lastMonUpdate=millis();
    blinkState   =false;
}


void drawBootScreen() {
    M5Cardputer.Display.fillScreen(COLOR_BG);

    
    M5Cardputer.Display.setTextColor(COLOR_CYAN);
    M5Cardputer.Display.drawString("  SD SECURITY", 2, 8);

    
    M5Cardputer.Display.drawLine(0, 24, 240, 24, COLOR_HEADER);

    
    M5Cardputer.Display.setTextColor(COLOR_PURPLE);
    M5Cardputer.Display.drawString(" FIRMWARE  V8.3", 2, 30);

    
    M5Cardputer.Display.drawLine(0, 45, 240, 45, COLOR_GRAY);

    
    M5Cardputer.Display.setTextColor(COLOR_TEXT);
    M5Cardputer.Display.drawString("> Evil Twin Detect", 4, 52);
    M5Cardputer.Display.drawString("> Deauth Monitor",   4, 66);
    M5Cardputer.Display.drawString("> Live Packet Scan", 4, 80);
    M5Cardputer.Display.drawString("> Attack Logging",   4, 94);

    
    M5Cardputer.Display.drawLine(0, 112, 240, 112, COLOR_HEADER);

    
    M5Cardputer.Display.setTextColor(COLOR_WARN);
    M5Cardputer.Display.drawString("  Initializing...", 2, 118);

    
    for(int i=0; i<3; i++){
        vTaskDelay(pdMS_TO_TICKS(300));
        M5Cardputer.Display.fillRect(0, 118, 240, 16, COLOR_BG);
        vTaskDelay(pdMS_TO_TICKS(200));
        M5Cardputer.Display.setTextColor(COLOR_WARN);
        M5Cardputer.Display.drawString("  Initializing...", 2, 118);
    }

    vTaskDelay(pdMS_TO_TICKS(400));

    
    M5Cardputer.Display.fillRect(0, 118, 240, 16, COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_SAFE);
    M5Cardputer.Display.drawString("   SYSTEM READY!", 2, 118);
    vTaskDelay(pdMS_TO_TICKS(700));
}


void performScan() {
    M5Cardputer.Display.fillScreen(COLOR_BG);

    
    M5Cardputer.Display.setTextColor(COLOR_CYAN);
    M5Cardputer.Display.drawString("SD SECURITY - SCAN", 2, 2);
    M5Cardputer.Display.drawLine(0, 14, 240, 14, COLOR_HEADER);

    allNets.clear();

    WiFi.mode(WIFI_OFF);   vTaskDelay(pdMS_TO_TICKS(200));
    WiFi.mode(WIFI_STA);   vTaskDelay(pdMS_TO_TICKS(300));
    WiFi.disconnect(true); vTaskDelay(pdMS_TO_TICKS(300));

    auto addNet=[&](int i){
        if(!bssidExists(WiFi.BSSID(i))){
            WiFiNetwork net;
            net.ssid   =WiFi.SSID(i);
            net.rssi   =WiFi.RSSI(i);
            net.encType=WiFi.encryptionType(i);
            net.channel=WiFi.channel(i);
            WiFi.BSSID(i,net.bssid);
            allNets.push_back(net);
        }
    };

    M5Cardputer.Display.setTextColor(COLOR_TEXT);
    M5Cardputer.Display.drawString("Pass 1/4 Standard",2,22);
    int n=WiFi.scanNetworks(false,true,false,400);
    if(n>0) for(int i=0;i<n;i++) addNet(i);
    WiFi.scanDelete();
    M5Cardputer.Display.setTextColor(COLOR_SAFE);
    char b1[22]; sprintf(b1,"OK -> %d networks",(int)allNets.size());
    M5Cardputer.Display.drawString(b1,2,33);

    M5Cardputer.Display.setTextColor(COLOR_TEXT);
    M5Cardputer.Display.drawString("Pass 2/4 Deep",2,48);
    n=WiFi.scanNetworks(false,true,false,700);
    if(n>0) for(int i=0;i<n;i++) addNet(i);
    WiFi.scanDelete();
    M5Cardputer.Display.setTextColor(COLOR_SAFE);
    char b2[22]; sprintf(b2,"OK -> %d networks",(int)allNets.size());
    M5Cardputer.Display.drawString(b2,2,59);

    M5Cardputer.Display.setTextColor(COLOR_TEXT);
    M5Cardputer.Display.drawString("Pass 3/4 Passive",2,74);
    n=WiFi.scanNetworks(false,true,true,600);
    if(n>0) for(int i=0;i<n;i++) addNet(i);
    WiFi.scanDelete();
    M5Cardputer.Display.setTextColor(COLOR_SAFE);
    char b3[22]; sprintf(b3,"OK -> %d networks",(int)allNets.size());
    M5Cardputer.Display.drawString(b3,2,85);

    M5Cardputer.Display.setTextColor(COLOR_TEXT);
    M5Cardputer.Display.drawString("Pass 4/4 Channel",2,100);

    for(int ch=1;ch<=13;ch++) {
        M5Cardputer.Display.fillRect(2,111,150,11,COLOR_BG);
        M5Cardputer.Display.setTextColor(COLOR_WARN);
        char cb[18]; sprintf(cb,"CH %2d / 13 ...",ch);
        M5Cardputer.Display.drawString(cb,2,111);
        wifi_scan_config_t cfg;
        memset(&cfg,0,sizeof(cfg));
        cfg.channel             =ch;
        cfg.show_hidden         =true;
        cfg.scan_type           =WIFI_SCAN_TYPE_ACTIVE;
        cfg.scan_time.active.min=80;
        cfg.scan_time.active.max=200;
        if(esp_wifi_scan_start(&cfg,true)!=ESP_OK){
            esp_wifi_scan_stop(); continue;
        }
        uint16_t ac=0;
        esp_wifi_scan_get_ap_num(&ac);
        if(ac>0&&ac<=40){
            wifi_ap_record_t* r=(wifi_ap_record_t*)malloc(
                sizeof(wifi_ap_record_t)*ac);
            if(r){
                esp_wifi_scan_get_ap_records(&ac,r);
                for(int i=0;i<ac;i++){
                    if(!bssidExists(r[i].bssid)){
                        WiFiNetwork net;
                        net.ssid   =String((char*)r[i].ssid);
                        net.rssi   =r[i].rssi;
                        net.channel=r[i].primary;
                        memcpy(net.bssid,r[i].bssid,6);
                        net.encType=(uint8_t)r[i].authmode;
                        allNets.push_back(net);
                    }
                }
                free(r);
            }
        }
        esp_wifi_scan_stop();
        vTaskDelay(pdMS_TO_TICKS(8));
    }

    for(int i=0;i<(int)allNets.size()-1;i++)
        for(int j=i+1;j<(int)allNets.size();j++)
            if(allNets[j].rssi>allNets[i].rssi){
                auto t=allNets[i];allNets[i]=allNets[j];allNets[j]=t;
            }

    M5Cardputer.Display.fillRect(0,111,240,24,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_SAFE);
    char res[30]; sprintf(res,"Found: %d networks!",(int)allNets.size());
    M5Cardputer.Display.drawString(res,2,112);
    M5Cardputer.Display.setTextColor(COLOR_WHITE);
    M5Cardputer.Display.drawString("ENTER: Continue",2,122);

    lastScanTime=millis();
    menuState=1; listScroll=0; selIdx=0;
    scrollPos=0; scrollFwd=true;
    vTaskDelay(pdMS_TO_TICKS(800));
}


void prepareTests() {
    results.clear(); targetAPs.clear();
    totalScore=100; testStep=0;
    testRunning=true; testTimer=millis()-400;
    firstTestDraw=true; lastDrawnStep=-1;
    menuState=2; repScroll=0;
    for(auto& n:allNets)
        if(n.ssid==selectedSSID) targetAPs.push_back(n);
}

void runNextTest() {
    if(!testRunning||millis()-testTimer<350) return;
    testTimer=millis();
    TestResult r; r.score=0; r.severity=0;

    switch(testStep) {
        case 0:{
            r.name="1.Evil Twin";
            int c=targetAPs.size();
            if(c>2)      {r.severity=2;r.score=40;r.detail="CRIT!"+String(c)+" AP same SSID";}
            else if(c==2){r.severity=2;r.score=30;r.detail="DANGER!2 AP same SSID";}
            else          r.detail="Single AP.No EvilTwin";
            break;}
        case 1:{
            r.name="2.Encryption";
            uint8_t e=targetAPs.empty()?WIFI_AUTH_OPEN:targetAPs[0].encType;
            if(e==WIFI_AUTH_OPEN)        {r.severity=2;r.score=35;r.detail="OPEN!No encryption";}
            else if(e==WIFI_AUTH_WEP)    {r.severity=2;r.score=30;r.detail="WEP weak crackable";}
            else if(e==WIFI_AUTH_WPA_PSK){r.severity=1;r.score=15;r.detail="WPA weak protection";}
            else if(e==WIFI_AUTH_WPA2_PSK)r.detail="WPA2 good protection";
            else if(e==WIFI_AUTH_WPA3_PSK)r.detail="WPA3 strongest";
            else{r.severity=1;r.score=5;r.detail="Enc:"+encStr(e);}
            break;}
        case 2:{
            r.name="3.Signal Anomaly";
            if(targetAPs.empty()){r.severity=1;r.score=10;r.detail="No AP found";}
            else{
                int mx=-100;
                for(auto& a:targetAPs) if(a.rssi>mx) mx=a.rssi;
                if(mx>-25)      {r.severity=2;r.score=25;r.detail="TOO STRONG "+String(mx)+"dBm";}
                else if(mx>-40) {r.severity=1;r.score=10;r.detail="Strong "+String(mx)+"dBm";}
                else             r.detail="Normal "+String(mx)+"dBm";
            }
            break;}
        case 3:{
            r.name="4.Channel";
            if((int)targetAPs.size()>1){
                bool same=true; int c0=targetAPs[0].channel;
                for(auto& a:targetAPs) if(a.channel!=c0){same=false;break;}
                if(same){r.severity=1;r.score=10;r.detail="Same CH:"+String(c0);}
                else     r.detail="Diff channels OK";
            } else r.detail="Single AP channel OK";
            break;}
        case 4:{
            r.name="5.Deauth Risk";
            bool w3=false,op=false;
            for(auto& a:targetAPs){
                if(a.encType==WIFI_AUTH_WPA3_PSK) w3=true;
                if(a.encType==WIFI_AUTH_OPEN)     op=true;
            }
            if(op)       {r.severity=2;r.score=20;r.detail="OPEN!MITM max risk";}
            else if(!w3) {r.severity=1;r.score=10;r.detail="No WPA3.Deauth risk";}
            else          r.detail="WPA3 protected";
            break;}
        case 5:{
            r.name="6.Fake MAC";
            bool f=false; int ix=-1;
            for(int i=0;i<(int)targetAPs.size();i++)
                if(targetAPs[i].bssid[0]&0x02){f=true;ix=i;break;}
            if(f){r.severity=2;r.score=20;r.detail="AP"+String(ix+1)+" random MAC";}
            else  r.detail="MAC addresses normal";
            break;}
        case 6:{
            r.name="7.Env Density";
            int t=allNets.size();
            if(t>35){r.severity=1;r.score=5;r.detail=String(t)+" nets dense area";}
            else     r.detail=String(t)+" nets normal";
            break;}
        case 7:{
            r.name="8.BSSID Consist";
            if((int)targetAPs.size()>1){
                bool d=false;
                for(int i=1;i<(int)targetAPs.size();i++)
                    if(targetAPs[i].bssid[0]!=targetAPs[0].bssid[0]||
                       targetAPs[i].bssid[1]!=targetAPs[0].bssid[1])
                    {d=true;break;}
                if(d){r.severity=2;r.score=15;r.detail="Diff vendor!Fake?";}
                else  r.detail="Same vendor OK";
            } else r.detail="Single AP BSSID OK";
            break;}
        case 8:{
            r.name="9.Open Net Threat";
            int mc=targetAPs.empty()?0:targetAPs[0].channel,c=0;
            for(auto& net:allNets)
                if(net.ssid!=selectedSSID&&
                   net.encType==WIFI_AUTH_OPEN&&
                   net.channel==mc) c++;
            if(c>0){r.severity=1;r.score=10;r.detail=String(c)+" open nets same CH";}
            else    r.detail="No open net threat";
            break;}
        case 9:{
            r.name="10.Neighbor Intrf";
            int mc=targetAPs.empty()?0:targetAPs[0].channel;
            int myRssi=targetAPs.empty()?-100:targetAPs[0].rssi;
            int c=0;
            for(auto& net:allNets)
                if(net.ssid!=selectedSSID&&
                   net.channel==mc&&
                   net.rssi>myRssi+10) c++;
            if(c>0){r.severity=1;r.score=8;r.detail=String(c)+" strong nbr CH:"+String(mc);}
            else    r.detail="No neighbor interfere";
            break;}
        case 10:{
            r.name="11.Auth Strength";
            bool strong=false;
            for(auto& a:targetAPs)
                if(a.encType==WIFI_AUTH_WPA2_ENTERPRISE||
                   a.encType==WIFI_AUTH_WPA3_PSK) strong=true;
            if(strong) r.detail="WPA3/ENT strong auth";
            else{r.severity=1;r.score=5;r.detail="No strong auth(WPA2-)";}
            break;}
        case 11:{
            int d=0;
            for(auto& x:results) d+=x.score;
            totalScore=max(0,100-d);
            r.name="12.OVERALL SCORE";
            if(totalScore>=80)       r.detail="SCORE:"+String(totalScore)+"/100 LOW";
            else if(totalScore>=50) {r.severity=1;r.detail="SCORE:"+String(totalScore)+"/100 MED";}
            else                    {r.severity=2;r.detail="SCORE:"+String(totalScore)+"/100 HIGH";}
            testRunning=false;
            break;}
        default: testRunning=false; return;
    }
    r.name  =clip(r.name,  22);
    r.detail=clip(r.detail,22);
    results.push_back(r);
    testStep++;
}


void updateScroll() {
    if(millis()-lastScrollTime<SCROLL_SPEED) return;
    lastScrollTime=millis();
    if(allNets.empty()||selIdx>=(int)allNets.size()) return;
    String f=allNets[selIdx].ssid;
    if(!f.length()) f="[Hidden]";
    const int vl=9;
    if((int)f.length()<=vl){scrollPos=0;scrollFwd=true;return;}
    int mx=(int)f.length()-vl;
    if(scrollFwd){scrollPos++;if(scrollPos>=mx){scrollPos=mx;scrollFwd=false;}}
    else         {scrollPos--;if(scrollPos<=0) {scrollPos=0; scrollFwd=true;}}
}

String getSelSSID(int vl=9) {
    if(allNets.empty()) return "";
    String f=allNets[selIdx].ssid;
    if(!f.length()) f="[Hidden]";
    if((int)f.length()<=vl) return padR(f,vl);
    int p=constrain(scrollPos,0,(int)f.length()-vl);
    return padR(f.substring(p,p+vl),vl);
}

String getStatSSID(String s,int vl=9) {
    if(!s.length()) s="[Hidden]";
    return padR(s.length()>vl?s.substring(0,vl):s,vl);
}

void resetScroll(){scrollPos=0;scrollFwd=true;lastScrollTime=millis();}



void drawMainMenu() {
    M5Cardputer.Display.fillScreen(COLOR_BG);

    
    M5Cardputer.Display.setTextColor(COLOR_CYAN);
    M5Cardputer.Display.drawString("SD SECURITY V8.3", 2, 2);
    M5Cardputer.Display.drawLine(0, 14, 240, 14, COLOR_HEADER);

    
    M5Cardputer.Display.setTextColor(COLOR_TEXT);
    M5Cardputer.Display.drawString("> Evil Twin Detector",   2, 22);
    M5Cardputer.Display.drawString("> Deauth/MITM Analysis", 2, 36);
    M5Cardputer.Display.drawString("> Live Packet Monitor",  2, 50);
    M5Cardputer.Display.drawString("> Attack Detect & Log",  2, 64);

    
    M5Cardputer.Display.setTextColor(COLOR_WHITE);
    M5Cardputer.Display.drawString("ENTER:Scan  R:Refresh",  2, 82);

    i
    if(lastScanTime>0){
        M5Cardputer.Display.setTextColor(COLOR_WARN);
        char buf[34];
        sprintf(buf,"Last:%ds [%d nets]",
            (int)((millis()-lastScanTime)/1000),(int)allNets.size());
        M5Cardputer.Display.drawString(buf,2,100);
    }
}

void drawNetworkList() {
    M5Cardputer.Display.fillRect(0,0,240,14,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_CYAN);
    char hdr[26]; sprintf(hdr,"NETWORKS[%d]",(int)allNets.size());
    M5Cardputer.Display.drawString(hdr,2,2);
    char idx[12]; sprintf(idx,"%d/%d",selIdx+1,(int)allNets.size());
    M5Cardputer.Display.setTextColor(COLOR_WARN);
    M5Cardputer.Display.drawString(idx,195,2);
    M5Cardputer.Display.drawLine(0,14,240,14,COLOR_HEADER);
    M5Cardputer.Display.fillRect(0,15,240,103,COLOR_BG);
    M5Cardputer.Display.drawLine(0,118,240,118,COLOR_HEADER);
    M5Cardputer.Display.fillRect(0,119,240,15,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_WARN);
    M5Cardputer.Display.drawString(";/. Sel ENTER:Analyze",2,121);

    std::map<String,int> sc;
    for(auto& n:allNets) sc[n.ssid]++;

    const int COL_DUP=0, COL_SSID=36, COL_RSSI=144, COL_CH=195;
    const int vi=7, rh=14;
    int y=16;

    for(int i=listScroll;i<(int)allNets.size()&&i<listScroll+vi;i++){
        auto& net=allNets[i]; bool sel=(i==selIdx); int dup=sc[net.ssid];
        M5Cardputer.Display.fillRect(0,y-1,240,rh,sel?0x001F:COLOR_BG);
        uint16_t col;
        if(dup>1)                            col=COLOR_DANGER;
        else if(net.encType==WIFI_AUTH_OPEN) col=COLOR_WARN;
        else                                 col=COLOR_TEXT;
        M5Cardputer.Display.setTextColor(sel?COLOR_WHITE:col);
        M5Cardputer.Display.drawString(dup>1?"[!]":"   ",COL_DUP,y);
        String ds=sel?getSelSSID(9):getStatSSID(net.ssid,9);
        M5Cardputer.Display.drawString(ds,COL_SSID,y);
        char rssiStr[8]; sprintf(rssiStr,"%4d",net.rssi);
        M5Cardputer.Display.drawString(rssiStr,COL_RSSI,y);
        char chStr[6]; sprintf(chStr,"C%02d",(int)net.channel);
        M5Cardputer.Display.drawString(chStr,COL_CH,y);
        y+=rh;
    }
}

void drawTestScreen() {
    if(firstTestDraw){
        M5Cardputer.Display.fillScreen(COLOR_BG);
        M5Cardputer.Display.setTextColor(COLOR_CYAN);
        String ss=selectedSSID.length()>10?
                  selectedSSID.substring(0,9)+"~":selectedSSID;
        // SD SECURITY adı test ekranında da görünür
        M5Cardputer.Display.drawString("SDS:"+ss,2,2);
        M5Cardputer.Display.drawLine(0,14,240,14,COLOR_HEADER);
        M5Cardputer.Display.drawLine(0,117,240,117,COLOR_HEADER);
        firstTestDraw=false; lastDrawnStep=-1;
    }
    if(!results.empty()&&(int)results.size()-1!=lastDrawnStep){
        lastDrawnStep=(int)results.size()-1;
        const int lh=17,sy=16,ey=116;
        const int vis=(ey-sy)/lh;
        int startI=max(0,(int)results.size()-vis);
        M5Cardputer.Display.fillRect(0,sy,240,ey-sy,COLOR_BG);
        int y=sy;
        for(int i=startI;i<(int)results.size()&&y+lh<=ey;i++){
            auto& r=results[i];
            uint16_t col; String icon;
            if(r.severity==2)      {col=COLOR_DANGER;icon="X";}
            else if(r.severity==1) {col=COLOR_WARN;  icon="!";}
            else                   {col=COLOR_SAFE;  icon="v";}
            M5Cardputer.Display.setTextColor(col);
            M5Cardputer.Display.drawString("["+icon+"]"+clip(r.name,19),0,y);
            M5Cardputer.Display.setTextColor(COLOR_WHITE);
            M5Cardputer.Display.drawString("    "+clip(r.detail,21),0,y+8);
            y+=lh;
        }
    }
    M5Cardputer.Display.fillRect(0,118,240,16,COLOR_BG);
    M5Cardputer.Display.drawLine(0,117,240,117,COLOR_HEADER);
    if(testRunning){
        M5Cardputer.Display.setTextColor(COLOR_CYAN);
        static uint8_t dot=0; dot=(dot+1)%4;
        char dots[5]={0}; for(int d=0;d<dot;d++) dots[d]='.';
        char bar[32]; sprintf(bar,"Test %d/12 %s",testStep,dots);
        M5Cardputer.Display.drawString(bar,2,120);
    } else {
        M5Cardputer.Display.setTextColor(COLOR_SAFE);
        M5Cardputer.Display.drawString("ENTER:Report M:Monitor",2,120);
    }
}

void drawReport() {
    M5Cardputer.Display.fillRect(0,0,240,14,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_CYAN);
    String ss=selectedSSID.length()>8?
              selectedSSID.substring(0,7)+"~":selectedSSID;
    
    M5Cardputer.Display.drawString("SDS:"+ss,2,2);
    uint16_t sc2=totalScore>=80?COLOR_SAFE:totalScore>=50?COLOR_WARN:COLOR_DANGER;
    M5Cardputer.Display.setTextColor(sc2);
    char scoreBuf[14]; sprintf(scoreBuf,"%3d/100",totalScore);
    M5Cardputer.Display.drawString(scoreBuf,185,2);
    M5Cardputer.Display.drawLine(0,14,240,14,COLOR_HEADER);
    M5Cardputer.Display.drawLine(0,117,240,117,COLOR_HEADER);
    M5Cardputer.Display.fillRect(0,118,240,16,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_WARN);
    M5Cardputer.Display.drawString(";/.:Scroll M:Mon Q:Back",2,120);
    const int mv=4;
    M5Cardputer.Display.setTextColor(COLOR_GRAY);
    char pg[16];
    sprintf(pg,"%d-%d/%d",repScroll+1,
        min((int)results.size(),repScroll+mv),(int)results.size());
    M5Cardputer.Display.drawString(pg,170,2);
    M5Cardputer.Display.fillRect(0,15,240,102,COLOR_BG);
    const int lh=22; int y=16;
    for(int i=repScroll;i<(int)results.size()&&i<repScroll+mv;i++){
        auto& r=results[i];
        uint16_t col; String icon;
        if(r.severity==2)      {col=COLOR_DANGER;icon="[X]";}
        else if(r.severity==1) {col=COLOR_WARN;  icon="[!]";}
        else                   {col=COLOR_SAFE;  icon="[v]";}
        M5Cardputer.Display.fillRect(0,y-1,240,lh,
            r.severity==2?0x3000:r.severity==1?0x2800:COLOR_BG);
        M5Cardputer.Display.setTextColor(col);
        M5Cardputer.Display.drawString(icon+" "+clip(r.name,19),2,y);
        if(r.score>0){
            M5Cardputer.Display.setTextColor(COLOR_DANGER);
            char sc[6]; sprintf(sc,"-%d",r.score);
            M5Cardputer.Display.drawString(sc,210,y);
        }
        M5Cardputer.Display.setTextColor(COLOR_WHITE);
        M5Cardputer.Display.drawString("    "+clip(r.detail,21),2,y+11);
        M5Cardputer.Display.drawLine(0,y+lh-2,240,y+lh-2,0x2104);
        y+=lh;
    }
}

void drawMonitorScreen(bool full) {
    if(full){
        M5Cardputer.Display.fillScreen(COLOR_BG);
    }
    M5Cardputer.Display.setTextSize(1);

    if(full){
        M5Cardputer.Display.fillRect(0,0,240,14,COLOR_BG);
        M5Cardputer.Display.setTextColor(COLOR_CYAN);
        String ss = selectedSSID.length()>6 ?
                    selectedSSID.substring(0,5)+"~" : selectedSSID;
        char hdrBuf[28];
        
        sprintf(hdrBuf,"SDS-MON:%-6s CH:%d",
                ss.c_str(), monitorChannel);
        M5Cardputer.Display.drawString(clip(String(hdrBuf),22),2,2);
        M5Cardputer.Display.drawLine(0,14,240,14,COLOR_HEADER);
    }

    
    M5Cardputer.Display.fillRect(0,15,240,16,COLOR_BG);
    if(attackDetected){
        blinkState=!blinkState;
        M5Cardputer.Display.fillRect(0,15,240,16,
            blinkState ? COLOR_DANGER : 0x5000);
        M5Cardputer.Display.setTextColor(COLOR_WHITE);
        char atk[22];
        sprintf(atk,"!! ATTACK !! %3dp/s", packetsPerSecond);
        M5Cardputer.Display.drawString(atk, 4, 17);
    } else {
        M5Cardputer.Display.fillRect(0,15,240,16,0x0320);
        M5Cardputer.Display.setTextColor(COLOR_SAFE);
        char safe[22];
        sprintf(safe,"Secure  CH:%d  p/s:%d",
                monitorChannel, packetsPerSecond);
        M5Cardputer.Display.drawString(clip(String(safe),21), 4, 17);
    }

    
    M5Cardputer.Display.fillRect(0,33,240,14,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_CYAN);
    char row1[26];
    sprintf(row1,"D:%-3d DS:%-3d ET:%-2d",
            deauthCount, disassocCount, evilTwinCount);
    M5Cardputer.Display.drawString(clip(String(row1),20), 2, 34);

    
    M5Cardputer.Display.fillRect(0,49,240,14,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_PURPLE);
    char row2[26];
    sprintf(row2,"Mgmt:%-5u Dat:%-5u",
            (unsigned)totalMgmtCount,
            (unsigned)totalDataCount);
    M5Cardputer.Display.drawString(clip(String(row2),21), 2, 50);

    
    M5Cardputer.Display.fillRect(0,65,240,14,COLOR_BG);
    unsigned long now2=millis();
    int activeAtk=0, bestIdx=-1;
    uint32_t maxPkt=0;
    for(int i=0;i<attackerCount;i++){
        if(attackerTable[i].active &&
           (now2-attackerTable[i].lastSeen)<6000){
            activeAtk++;
            if(attackerTable[i].packetCount>maxPkt){
                maxPkt=attackerTable[i].packetCount;
                bestIdx=i;
            }
        }
    }
    if(activeAtk>0 && bestIdx>=0){
        M5Cardputer.Display.setTextColor(COLOR_ORANGE);
        auto& a=attackerTable[bestIdx];
        char atkLine[26];
        if(!a.apSSID.isEmpty()){
            char sb[7]; strncpy(sb,a.apSSID.c_str(),6); sb[6]=0;
            sprintf(atkLine,"ATK:%d %02X:%02X:%02X >%s",
                    activeAtk,
                    a.mac[3],a.mac[4],a.mac[5],
                    sb);
        } else {
            sprintf(atkLine,"ATK:%d %02X:%02X:%02X:%02X",
                    activeAtk,
                    a.mac[2],a.mac[3],
                    a.mac[4],a.mac[5]);
        }
        M5Cardputer.Display.drawString(clip(String(atkLine),21), 2, 66);
    } else {
        M5Cardputer.Display.setTextColor(COLOR_GRAY);
        M5Cardputer.Display.drawString("No active attacker", 2, 66);
    }

    
    M5Cardputer.Display.drawLine(0,81,240,81,COLOR_HEADER);

    
    M5Cardputer.Display.fillRect(0,82,240,34,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_GRAY);
    M5Cardputer.Display.drawString("-- LAST EVENT --", 2, 83);

    if(!hasEvent){
        M5Cardputer.Display.setTextColor(COLOR_GRAY);
        M5Cardputer.Display.drawString("No events yet...", 2, 99);
    } else {
        auto& ev = lastEvent;
        uint16_t col;
        if     (ev.type=="DEAUTH")     col=COLOR_DANGER;
        else if(ev.type=="DISASSOC")   col=COLOR_ORANGE;
        else if(ev.type=="EVIL TWIN")  col=COLOR_PURPLE;
        else if(ev.type=="SYSTEM")     col=COLOR_CYAN;
        else                           col=COLOR_WARN;

        M5Cardputer.Display.setTextColor(col);
        char l1[26];
        uint32_t age=(uint32_t)(millis()/1000 - ev.timestamp);
        if(ev.count>1)
            sprintf(l1,"[%s]x%u %us",
                    ev.type.c_str(),(unsigned)ev.count,(unsigned)age);
        else
            sprintf(l1,"[%s] %us ago",
                    ev.type.c_str(),(unsigned)age);
        M5Cardputer.Display.drawString(clip(String(l1),21), 2, 99);

        M5Cardputer.Display.setTextColor(COLOR_WHITE);
        M5Cardputer.Display.drawString(clip(ev.detail,21), 2, 113);
    }

    
    M5Cardputer.Display.drawLine(0,117,240,117,COLOR_HEADER);

    
    M5Cardputer.Display.fillRect(0,118,240,17,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_WARN);
    M5Cardputer.Display.drawString("Q:Back ENTER:Exit Mon",2,120);
}

void drawAPDetail() {
    M5Cardputer.Display.fillScreen(COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_CYAN);
    String ss=selectedSSID.length()>12?
              selectedSSID.substring(0,11)+"~":selectedSSID;
    M5Cardputer.Display.drawString("AP:"+ss,2,2);
    M5Cardputer.Display.drawLine(0,14,240,14,COLOR_HEADER);
    int y=17;
    for(int i=0;i<(int)targetAPs.size()&&y<112;i++){
        auto& ap=targetAPs[i];
        M5Cardputer.Display.setTextColor(i==0?COLOR_TEXT:COLOR_DANGER);
        M5Cardputer.Display.drawString(
            "--AP"+String(i+1)+(i>0?" [SUSPECT!]":" [Main]"),2,y); y+=13;
        M5Cardputer.Display.setTextColor(COLOR_WHITE);
        M5Cardputer.Display.drawString(
            "MAC:"+bssidStr(ap.bssid),2,y); y+=13;
        char buf[28];
        sprintf(buf,"RSSI:%ddBm CH:%d %s",
            ap.rssi,(int)ap.channel,encStr(ap.encType).c_str());
        M5Cardputer.Display.drawString(clip(String(buf),21),2,y); y+=14;
    }
    M5Cardputer.Display.drawLine(0,117,240,117,COLOR_HEADER);
    M5Cardputer.Display.fillRect(0,118,240,16,COLOR_BG);
    M5Cardputer.Display.setTextColor(COLOR_WARN);
    M5Cardputer.Display.drawString("ENTER:Back to Report",2,120);
}


void setup() {
    auto cfg=M5.config();
    M5Cardputer.begin(cfg);
    M5Cardputer.Display.setRotation(1);
    M5Cardputer.Display.fillScreen(COLOR_BG);
    M5Cardputer.Display.setTextFont(&fonts::FreeMono9pt7b);
    M5Cardputer.Display.setTextSize(1);

    WiFi.mode(WIFI_STA);
    WiFi.disconnect();
    vTaskDelay(pdMS_TO_TICKS(200));

    
    drawBootScreen();

    menuState=0;
    drawMainMenu();
}

void loop() {
    M5Cardputer.update();

    if(menuState==5){
        updateMonitor();
        if(millis()-lastBlinkTime>350){
            lastBlinkTime=millis();
            drawMonitorScreen(false);
        }
    }

    if(menuState==2&&testRunning){
        runNextTest();
        drawTestScreen();
    }

    if(menuState==1){
        updateScroll();
        static int lsp=-1;
        if(scrollPos!=lsp){lsp=scrollPos;drawNetworkList();}
    }

    if(millis()-lastKeyTime<160) return;
    if(!M5Cardputer.Keyboard.isChange()) return;
    if(!M5Cardputer.Keyboard.isPressed()) return;
    lastKeyTime=millis();

    auto status=M5Cardputer.Keyboard.keysState();
    bool nd=false;

    if(status.enter){
        if(menuState==0)                       {performScan();nd=true;}
        else if(menuState==1&&!allNets.empty()){
            selectedSSID=allNets[selIdx].ssid;prepareTests();nd=true;}
        else if(menuState==2&&!testRunning)    {menuState=3;nd=true;}
        else if(menuState==3)                  {menuState=1;nd=true;}
        else if(menuState==4)                  {menuState=3;nd=true;}
        else if(menuState==5){stopPromiscuous();menuState=3;nd=true;}
    }

    if(keyInExact(status.word,';')){
        if(menuState==1&&selIdx>0){
            selIdx--;if(selIdx<listScroll)listScroll--;
            resetScroll();nd=true;
        } else if(menuState==3&&repScroll>0){repScroll--;nd=true;}
    }

    if(keyInExact(status.word,'.')){
        if(menuState==1&&selIdx<(int)allNets.size()-1){
            selIdx++;if(selIdx>=listScroll+7)listScroll++;
            resetScroll();nd=true;
        } else if(menuState==3&&repScroll<(int)results.size()-1){
            repScroll++;nd=true;
        }
    }

    if(keyIn(status.word,'r')&&menuState!=5){
        stopPromiscuous();menuState=0;performScan();nd=true;
    }

    if(keyIn(status.word,'m')&&(menuState==2||menuState==3)){
        startMonitor();drawMonitorScreen(true);
    }

    if(keyIn(status.word,'d')&&menuState==3){menuState=4;nd=true;}

    if(keyIn(status.word,'q')){
        if(menuState==5){stopPromiscuous();menuState=3;nd=true;}
        else if(menuState==4||menuState==3){menuState=1;nd=true;}
        else if(menuState==1){menuState=0;nd=true;}
    }

    if(nd){
        switch(menuState){
            case 0:drawMainMenu();         break;
            case 1:drawNetworkList();      break;
            case 2:drawTestScreen();       break;
            case 3:drawReport();           break;
            case 4:drawAPDetail();         break;
            case 5:drawMonitorScreen(true);break;
        }
    }
}
