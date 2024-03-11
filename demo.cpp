
#include <unistd.h>
#include <signal.h>
// #include "jetsonEncoder.h"
#include "serialport.h"
#include <queue>
#include "common.h"
#include <sstream>
#include <cmath>
#include "camera.h"
#include "painter.h"
#include <arpa/inet.h>
#include <sys/vfs.h>
#include <yaml-cpp/yaml.h>
#include "realtracker.h"
#include "spdlog/spdlog.h"
#include "spdlog/stopwatch.h"
#include <deque>
#include <numeric>

extern ST_A1_CONFIG stA1Cfg;
extern ST_A2_CONFIG stA2Cfg;
extern ST_C1_CONFIG stC1Cfg;
extern ST_C2_CONFIG stC2Cfg;
extern ST_E1_CONFIG stE1Cfg;
extern ST_E2_CONFIG stE2Cfg;
extern ST_S1_CONFIG stS1Cfg;
extern ST_S2_CONFIG stS2Cfg;
extern ST_U_CONFIG stUCfg;
extern ST_A1C1E1_CONFIG stA1C1E1Cfg;
extern ST_A2C2E2_CONFIG stA2C2E2Cfg;
extern ST_A1C1E1S1_CONFIG stA1C1E1S1Cfg;
extern ST_A2C2E2S2_CONFIG stA2C2E2S2Cfg;
extern ST_T1F1B1D1_CONFIG stT1F1B1D1Cfg;
extern ST_T2F2B2D2_CONFIG stT2F2B2D2Cfg;

ST_SYS_STATUS stSysStatus;

#define DEBUG_SERIAL 1

void serialViewLinkFunc();

void serialSonyFunc();

void SaveRecordVideoFunc();

std::atomic<bool> interrupted(false);

void signalHandler(int signum)
{
    // 处理中断信号
    std::cout << "Signal " << signum << " caught, setting the interrupted flag to true." << std::endl;
    interrupted.store(true);
}

// viewlink通信串口，接收sony相机通信串口，发送sony相机通信串口
Serial serialViewLink, serialRevSony, serialSendSony;

SerialPort serialTCP;
// 线程同步条件变量
std::condition_variable saveVideoconVar, rtspconVar, OSDconVar, frameVar;
// 线程同步互斥变量
std::mutex m_mtx, rtspMtx, OSDMtx, detectAndTrackMtx, frameMtx, trackMtx;
// 是否存储视频变量
bool isRecording = false;
// 是否存储图片变量
bool isNeedTakePhoto = false;

// 用于推流以及保存视频的全局变量视频帧
cv::Mat saveFrame, rtspFrame, OSDFrame;

// 保存视频的writer
cv::VideoWriter *writer = nullptr;

// 用于推流的writer
cv::VideoWriter rtspWriterr;

// 用于控制伺服在目标中心小范围的时候锁定的变量
bool inObjCenterLock = false;

// TCP客户端连接句柄
int client_sockfd;

// 存储UDP客户端地址信息
struct sockaddr_in remote_addr;
// UDP客户端连接句柄
int server_sockfd;

realtracker *rtracker;

// 变焦调整波门大小
int zoomGrade = 1;
bool zoomFlag = false;

// UDP或TCP传输标识
bool TCPtransform = true;

static void cvtIrImg(cv::Mat &img, EN_IRIMG_MODE mode)
{

    if (mode == EN_IRIMG_MODE::BLACKHOT)
    {
        cv::cvtColor(img, img, cv::COLOR_RGB2GRAY);
        img = 255 - img;
        cv::cvtColor(img, img, cv::COLOR_GRAY2RGB);
    }
    else if (mode == EN_IRIMG_MODE::PSEUDOCOLOR)
    {
        cv::applyColorMap(img, img, cv::COLORMAP_HOT);
    }
}

static std::string CreateDirAndReturnCurrTimeStr(std::string folderName)
{
    std::string cmd = "mkdir " + folderName;
    int ret = system(cmd.c_str());
    printf("create %s dir result is %s\n", folderName.c_str(), (ret == 0) ? "success" : "failed");
    std::time_t curr = std::chrono::system_clock::to_time_t(std::chrono::system_clock::now());
    std::stringstream ss;
    ss << std::put_time(std::localtime(&curr), "%Y-%m-%d-%H-%M-%S");
    std::string currTime(ss.str());
    return currTime;
}

// 跟踪脱靶量向上位机反馈
static void TrackerMissDistanceResultFeedbackToDown(uint8_t *buf)
{
    uint8_t sendBuf[15] = {0};
    int sendBufLen = 15;
    sendBuf[0] = 0x55;
    sendBuf[1] = 0xAA;
    sendBuf[2] = 0xDC;
    sendBuf[3] = 0X0C;
    sendBuf[4] = 0x66;

    stSysStatus.trackMissDistance[0] = (buf[0] << 8) ^ buf[1];
    stSysStatus.trackMissDistance[1] = (buf[2] << 8) ^ buf[3];

    memcpy(sendBuf + 5, buf, 9);

    sendBuf[14] = viewlink_protocal_checksum(sendBuf);
    serialViewLink.serial_send(sendBuf, sendBufLen);
}

// 用于打印字节流为十六进制格式
void printHex(uint8_t *buffer, size_t length)
{
    for (size_t i = 0; i < length; i++)
    {
        printf("%02x ", buffer[i]);
    }
    printf("\n");
}

// TCP服务端线程程序，收到TCP消息解析后转发至小板串口
void TCP2serialFunc()
{

    struct sockaddr_in my_addr;
    struct sockaddr_in remote_addr;
    socklen_t sin_size;
    uint8_t recv_buf[BUFSIZ];
    uint8_t send_buf[BUFSIZ];
    memset(&my_addr, 0, sizeof(my_addr));
    my_addr.sin_family = AF_INET;
    my_addr.sin_addr.s_addr = INADDR_ANY;
    my_addr.sin_port = htons(2001);

    if ((server_sockfd = socket(PF_INET, SOCK_STREAM, 0)) < 0)
    {
        std::cout << "socket error" << std::endl;
        return;
    }

    if (bind(server_sockfd, (struct sockaddr *)&my_addr, sizeof(struct sockaddr)) < 0)
    {
        std::cout << "bind error" << std::endl;
        return;
    }

    if (listen(server_sockfd, 5) < 0)
    {
        std::cout << "listen error" << std::endl;
        return;
    }

    std::cout << "Server is listening on port ..." << std::endl;

    std::vector<uint8_t> receiveBuffer;
    const std::vector<uint8_t> frameStart = {0xeb, 0x90};
    const std::vector<uint8_t> frameStart_2 = {0x55, 0xaa, 0xdc};

    while (!interrupted.load())
    { // Main accept() loop
        sin_size = sizeof(struct sockaddr_in);
        if ((client_sockfd = accept(server_sockfd, (struct sockaddr *)&remote_addr, &sin_size)) < 0)
        {
            std::cout << "accept error" << std::endl;
            continue; // Continue to the next iteration to accept a new connection
        }

        std::cout << "Accepted client " << inet_ntoa(remote_addr.sin_addr) << std::endl;
        // send(client_sockfd, "Welcome to server", 17, 0);

        while (!interrupted.load())
        { // Communication loop
            memset(recv_buf, 0, BUFSIZ);
            ssize_t retLen = recv(client_sockfd, recv_buf, BUFSIZ, 0);
            if (retLen > 0)
            {
                TCPtransform = true;
                // receiveBuffer.insert(receiveBuffer.end(), recv_buf_temp, recv_buf_temp + retLen);
                serialTCP.serial_send(recv_buf + 3, retLen - 4);
                // printf("==============>");
                // printHex(recv_buf, retLen);
            }
        }

        close(client_sockfd); // Close the client socket before waiting for next connection
        std::cout << "Waiting for new connection..." << std::endl;
    }
}

// 从小板接收的串口数据封装成TCP消息，向上位机发送
void serial2TCPFunc()
{

    uint8_t buffRcvData[1024] = {0};
    uint8_t buffRcvData_[1024] = {0};
    int retLen = 0;
    std::vector<uint8_t> receiveBuffer;
    const std::vector<uint8_t> frameStart = {0x55, 0xAA, 0xDC};
    buffRcvData[0] = 0xEB;
    buffRcvData[1] = 0x90;

    while (!interrupted.load())
    {
        if (TCPtransform)
        {
            retLen = serialTCP.serial_receive(buffRcvData + 3);

            if (retLen > 0)
            {
                // printf("<===================");
                // printHex(buffRcvData + 3, retLen);
                // std::cout << std::endl;
                buffRcvData[2] = retLen & 0xFF;
                buffRcvData[retLen + 3] = viewlink_protocal_tcp_checksum(buffRcvData + 2);
                int len = send(client_sockfd, buffRcvData, 4 + retLen, 0);
            }
        }
    }
}
uint16_t UDPSendPort;
// UDP接收上位机消息
void UDP2serialFunc()
{

    struct sockaddr_in my_addr;

    socklen_t sin_size;
    uint8_t recv_buf[BUFSIZ];

    // 初始化地址信息
    memset(&my_addr, 0, sizeof(my_addr));
    my_addr.sin_family = AF_INET;
    my_addr.sin_addr.s_addr = INADDR_ANY;
    my_addr.sin_port = htons(UDPSendPort);

    // 创建UDP socket
    if ((server_sockfd = socket(PF_INET, SOCK_DGRAM, 0)) < 0)
    {
        std::cout << "socket error" << std::endl;
        return;
    }

    // 绑定socket到指定的端口和任意地址
    if (bind(server_sockfd, (struct sockaddr *)&my_addr, sizeof(struct sockaddr)) < 0)
    {
        std::cout << "bind error" << std::endl;
        return;
    }

    std::cout << "Server is listening on port 2000 for UDP traffic..." << std::endl;

    while (!interrupted.load())
    {
        sin_size = sizeof(struct sockaddr_in);
        // 接受来自客户端的数据
        ssize_t len = recvfrom(server_sockfd, recv_buf, BUFSIZ, 0, (struct sockaddr *)&remote_addr, &sin_size);
        if (len > 0)
        {
            TCPtransform = false;
            // std::cout << "Received packet from " << inet_ntoa(remote_addr.sin_addr) << std::endl;
            serialTCP.serial_send(recv_buf + 3, len - 4);
        }
    }

    close(server_sockfd); // 关闭socket
}

// 从小板接收的串口数据封装成UDP消息，向上位机发送
void serial2UDPFunc()
{
    uint8_t buffRcvData[1024] = {0};
    int retLen = 0;
    memset(buffRcvData, 0, sizeof(buffRcvData));
    buffRcvData[0] = 0xeb;
    buffRcvData[1] = 0x90;
    std::vector<uint8_t> receiveBuffer;
    const std::vector<uint8_t> frameStart = {0x55, 0xAA, 0xDC};

    while (!interrupted.load())
    {
        if (TCPtransform == false)
        {
            retLen = serialTCP.serial_receive(buffRcvData + 3);

            if (retLen > 0)
            {
                buffRcvData[2] = retLen & 0xFF; // 假设长度可以用一个字节表示
                buffRcvData[retLen + 3] = viewlink_protocal_tcp_checksum(buffRcvData + 3);

                // 发送数据到客户端
                socklen_t addrlen = sizeof(remote_addr); // 客户端地址长度
                sendto(server_sockfd, buffRcvData, retLen + 4, 0, (struct sockaddr *)&remote_addr, addrlen);
            }
        }
    }
}

// 绘制OSD线程以及推流
void osdAndSendRTSPStreamFunc()
{
    // 循环等待主线程的通知
    cv::Mat frame, dispFrame;
    while (!interrupted.load())
    {

        // 在界面上绘制OSD
        {
            std::unique_lock<std::mutex> lock(OSDMtx);
            OSDconVar.wait(lock);
            frame = OSDFrame.clone();
        }
        // 在界面上绘制OSD
        // stSysStatus.osdSet1Ctrl.enOSDShow = true;
        if (!stSysStatus.osdCtrl.osdSwitch)
        {
            if (!stSysStatus.osdCtrl.attitudeAngleSwitch)
            {
                // 绘制吊舱当前方位角度滚轴
                PaintRollAngleAxis(frame, stSysStatus.rollAngle);

                // 绘制吊舱当前俯仰角度滚轴
                PaintPitchAngleAxis(frame, stSysStatus.pitchAngle);
            }
            if (!stSysStatus.osdCtrl.crosshairSwitch)
            {
                // 绘制中心十字`
                PaintCrossPattern(frame, stSysStatus.rollAngle, stSysStatus.pitchAngle);
            }
            if (!stSysStatus.osdCtrl.GPSSwitch)
            {
                // 绘制经纬度、海拔高度等坐标参数
                PaintCoordinate(frame);
            }

            // 绘制界面上其他参数
            PaintViewPara(frame);
            if (!stSysStatus.osdCtrl.MissToTargetSwitch)
            {
                // 绘制脱靶量
                PaintTrackerMissDistance(frame);
            }
        }

        cv::resize(frame, dispFrame, cv::Size(1280, 720), cv::INTER_NEAREST);
        if (isRecording)
        {
            std::unique_lock<std::mutex> lock(m_mtx);
            saveFrame = dispFrame.clone();
        }

        if (isNeedTakePhoto)
        {
            std::string currTimeStr = CreateDirAndReturnCurrTimeStr("photos");
            std::string savePicFileName = "photos/" + currTimeStr + ".png";
            cv::imwrite(savePicFileName, dispFrame);
            isNeedTakePhoto = false;
        }

        if (!dispFrame.empty() && rtspWriterr.isOpened())
        {
            rtspWriterr << dispFrame;
        }
    }
}

// 多线程导致的图像延时，三线程会视频延时会增加两帧的延时
std::queue<cv::Mat> frameQueue;
uint8_t trackerStatus[9];
std::vector<bbox_t> g_detRet;
cv::Rect g_trackRect;

void detectAndTrackFunc()
{
    // 循环等待主线程的通知
    // cv::Mat frontFrame, backFrame;

    cv::Mat frontFrame = cv::Mat::zeros(1920, 1080, CV_8UC3);
    cv::Mat backFrame = cv::Mat::zeros(1920, 1080, CV_8UC3);
    cv::Rect trackRect;

    int center_x, center_y;
    bool detOn;

    // 产生的检测框vector
    std::vector<bbox_t> detRet;
    while (!interrupted.load())
    {
        detOn = true;

        {

            std::unique_lock<std::mutex> lock(frameMtx);
            frameVar.wait(lock);
            frontFrame = frameQueue.front().clone();
            backFrame = frameQueue.back().clone();
        }

        if (stSysStatus.trackOn)
        {
            detOn = false;
            if (!stSysStatus.trackerInited)
            {
                stSysStatus.detOn = false;
                spdlog::debug("start tracking, init Rect:");
                stSysStatus.trackerGateSize = stSysStatus.trackerGateSize * (sqrt(sqrt(zoomGrade)));
                zoomGrade = 1;
                rtracker->setGateSize(stSysStatus.trackerGateSize);
                rtracker->reset();
                rtracker->init(stSysStatus.trackAssignPoint, frontFrame, backFrame);
                stSysStatus.trackerInited = true;
            }
            else
            {
                rtracker->update(backFrame, frontFrame, detRet, trackerStatus, center_x, center_y, trackRect);
                {

                    std::unique_lock<std::mutex> lock(trackMtx);
                    g_trackRect = trackRect;
                }

                spdlog::debug("tracker status:{}", trackerStatus[4]);

                TrackerMissDistanceResultFeedbackToDown(trackerStatus);
                if (zoomFlag)
                {
                    stSysStatus.trackAssignPoint.x = center_x;
                    stSysStatus.trackAssignPoint.y = center_y;
                    stSysStatus.trackerInited = false;
                    zoomFlag = false;
                }
            }
        }
        if (detOn)
        {
            rtracker->runDetectorOut(backFrame, detRet);

            std::unique_lock<std::mutex> lock(detectAndTrackMtx);

            g_detRet = detRet;
        }
    }
}

// 预定义一个包含12种醒目颜色的列表
const std::vector<cv::Scalar> predefinedColors = {
    cv::Scalar(255, 0, 0),   // 红色
    cv::Scalar(0, 255, 0),   // 绿色
    cv::Scalar(0, 0, 255),   // 蓝色
    cv::Scalar(255, 255, 0), // 黄色
    cv::Scalar(255, 0, 255), // 粉色
    cv::Scalar(0, 255, 255), // 青色
    cv::Scalar(255, 127, 0), // 橙色
    cv::Scalar(127, 0, 255), // 紫色
    cv::Scalar(0, 127, 255), // 天蓝色
    cv::Scalar(127, 255, 0), // 酸橙色
    cv::Scalar(255, 0, 127), // 玫瑰红
    cv::Scalar(0, 255, 127), // 春绿色
    // ... 或许还可以添加更多的颜色，如果类别有增加
};

int main()
{
    // spdlog调试
    spdlog::set_level(spdlog::level::debug);
    spdlog::stopwatch sw;
    signal(SIGINT, signalHandler);

    //  fps统计变量
    std::deque<double> fpsCalculater;

    // 串口初始化
    serialViewLink.set_serial(1);                             //"/dev/ttyTHS1"
    serialRevSony.set_serial(2);                              //"/dev/ttyUSB0"
    serialSendSony.set_serial(3);                             //"/dev/ttyS6"
    serialTCP.set_serial("/dev/ttyUSB0", B115200, 8, 'N', 0); //"/dev/ttyS6"

    // 读取配置文件加载模型路径、设备名称等配置
    std::string cfgpath = "/home/rpdzkj/wjm/pinlingv2.3.1/exe/config.yaml";
    YAML::Node config = YAML::LoadFile(cfgpath);
    std::string visi_dev = config["visi_dev"].as<std::string>();
    std::string ir_dev = config["ir_dev"].as<std::string>();
    std::string rgbEngine = config["engine"].as<std::string>();
    std::string irEngine = config["irengine"].as<std::string>();
    std::string streamType = config["streamType"].as<std::string>();
    UDPSendPort = config["UDPSendPort"].as<uint16_t>();

    // rtsp推流变量
    if (streamType == "h264")
    {
        rtspWriterr.open("appsrc ! videoconvert ! video/x-raw,format=I420 ! mpph264enc ! video/x-h264 ! rtspclientsink location=rtsp://localhost:8553/stream", cv::CAP_GSTREAMER, 0, 60, cv::Size(1280, 720), true);
    }
    else if (streamType == "h265")
    {
        rtspWriterr.open("appsrc ! videoconvert ! video/x-raw,format=I420 ! mpph265enc ! video/x-h265 ! rtspclientsink location=rtsp://localhost:8553/stream", cv::CAP_GSTREAMER, 0, 60, cv::Size(1280, 720), true);
    }
    if (!rtspWriterr.isOpened())
    {
        printf("is not opened\n");
        return 0;
    }

    // 创建目标跟踪示例
    // rtracker = new realtracker(rgbEngine, irEngine, 12, 7);
    rtracker = new realtracker("/home/rpdzkj/wjm/pinlingv2.3.1/exe/trackercfg.yaml");

    // 开启viewlink串口线程，开启sony串口线程
    std::thread serialThViewLink = std::thread(serialViewLinkFunc);
    std::thread serialThSony = std::thread(serialSonyFunc);
    serialThSony.detach();
    serialThViewLink.detach();

    std::thread TCP2serialFuncTh = std::thread(TCP2serialFunc);
    TCP2serialFuncTh.detach();

    std::thread serial2TCPFuncTh = std::thread(serial2TCPFunc);
    serial2TCPFuncTh.detach();

    // 开启推流线程
    std::thread osdAndSendRTSPStreamTh(osdAndSendRTSPStreamFunc);
    osdAndSendRTSPStreamTh.detach();

    // 开启保存视频的线程
    std::thread SaveRecordVideoTh(SaveRecordVideoFunc);
    SaveRecordVideoTh.detach();

    // 开启检测跟踪视频的线程
    std::thread detectAndTrackTh(detectAndTrackFunc);
    detectAndTrackTh.detach();

    // UDP接收上位机消息至串口线程
    std::thread UDP2serialFuncTh(UDP2serialFunc);
    UDP2serialFuncTh.detach();

    // UDP发送串口消息至上位机线程
    std::thread serial2UDPFuncTh(serial2UDPFunc);
    serial2UDPFuncTh.detach();
    /*
        图像显示以及检测跟踪相关变量
    */
    // 需要目标检测的图像
    cv::Mat frame;

    // 帧数累加变量
    uint64_t nFrames = 0;

    // 初始化跟踪、检测以及显示模式
    stSysStatus.enDispMode = Vision;
    stSysStatus.trackOn = false;
    stSysStatus.detOn = false;

    // 画中画中小图像的起始点
    int pipPosX, pipPosY;

    // 可见光和红外图像的实例
    Camera *visCam = CreateCamera(visi_dev, 1920, 1080, std::string("mipi"));
    Camera *irCam = CreateCamera(ir_dev, 640, 512, std::string("GSTusb"));
    // Camera *irCam = CreateCamera(ir_dev, 640, 512, std::string("usb"));

    // 初始化红外图像
    cv::Mat oriIrImg = cv::Mat::zeros(640, 512, CV_8UC3);

    // 可见光图像
    cv::Mat rgbImg;

    int center_x, center_y;

    // 屏蔽上一次检测留在检测线程里的两帧检测框设立的检测帧数
    uint64_t DetFrameCount = 0;

    if (visCam != nullptr)
    {
        visCam->Init();
        printf("vis camera init success\n");
    }
    else
    {
        printf("vis camera init failed\n");
        return 0;
    }
    if (irCam != nullptr)
    {
        irCam->Init();
        printf("ir camera init success\n");
    }
    else
    {
        printf("ir camera init failed\n");
        return 0;
    }

    visCam->GetFrame(rgbImg);
    irCam->GetFrame(oriIrImg);

    if (oriIrImg.empty() || rgbImg.empty())
    {
        printf("input img empty, quit\n");
        return 0;
    }

    int irImgW = rgbImg.cols;
    int irImgH = rgbImg.rows;

    cv::Mat irImg = cv::Mat::zeros(irImgH, irImgW, CV_8UC3);

    int oriImgW = 1350;
    int oriImgH = 1080;

    int viImgW = rgbImg.cols;
    int viImgH = rgbImg.rows;

    pipPosX = (rgbImg.cols - oriImgW) / 2;
    pipPosY = (rgbImg.rows - oriImgH) / 2;

    rtracker->setFrameScale((double)viImgW / 1920);
    // 跟踪状态

    memset(trackerStatus, 0, 9);

    // 等待上次录制完成，需要进行录制标志
    bool isNeedRecording = false;

    uint64_t servoCommandSendCount = 0;

    stSysStatus.osdSet1Ctrl.enOSDShow = true;

    struct timeval time;
    long tmpTime, lopTime;
    gettimeofday(&time, nullptr);
    tmpTime, lopTime = time.tv_sec * 1000 + time.tv_usec / 1000;

    std::vector<bbox_t> detRet;

    while (!interrupted.load())
    {
        visCam->GetFrame(rgbImg);
        irCam->GetFrame(oriIrImg);

        if (oriIrImg.empty() || rgbImg.empty())
        {
            printf("input img empty, quit\n");
        }

        sw.reset();
        cvtIrImg(oriIrImg, stSysStatus.enIrImgMode);

        switch (stSysStatus.enDispMode)
        {
        case Vision: // 0x01
            frame = rgbImg;
            rtracker->setIrFrame(false);
            break;
        case Ir: // 0x02
            irImg.setTo(0);
            cv::resize(oriIrImg, oriIrImg, cv::Size(1350, 1080));
            oriIrImg.copyTo(irImg(cv::Rect(pipPosX, pipPosY, oriIrImg.cols, oriIrImg.rows)));
            frame = irImg;
            trackerStatus[4] |= 0x01; // 0000 0001
            rtracker->setIrFrame(true);
            break;
        case VisIrPip: // 0x03
            cv::resize(oriIrImg, oriIrImg, cv::Size(480, 360));
            oriIrImg.copyTo(rgbImg(cv::Rect(viImgW - 480, 0, 480, 360)));
            frame = rgbImg;
            rtracker->setIrFrame(false);
            break;
        case IrVisPip: // 0x04
            cv::resize(rgbImg, rgbImg, cv::Size(480, 360));
            cv::resize(oriIrImg, oriIrImg, cv::Size(1350, 1080));
            irImg.setTo(0);
            oriIrImg.copyTo(irImg(cv::Rect(pipPosX, pipPosY, oriIrImg.cols, oriIrImg.rows)));

            rgbImg.copyTo(irImg(cv::Rect(irImgW - 480, 0, 480, 360)));
            frame = irImg;
            // frame = rgbImg;
            rtracker->setIrFrame(true);
            break;
        default:
            frame = rgbImg;
            break;
        }

        {
            std::unique_lock<std::mutex> lock(frameMtx);
            frameQueue.push(frame.clone());
        }
        frameVar.notify_one();
        if (frameQueue.size() < 4)
        {
            continue;
        }

        if (stSysStatus.enScreenOpMode == EN_SCREEN_OP_MODE::SCREEN_SHOOT)
        {
            stSysStatus.enScreenOpMode = EN_SCREEN_OP_MODE::SCREEN_NONE;
            isNeedTakePhoto = true;
        }
        else if (stSysStatus.enScreenOpMode == EN_SCREEN_OP_MODE::RECORDING_START && !isRecording)
        {
            stSysStatus.enScreenOpMode = EN_SCREEN_OP_MODE::SCREEN_NONE;

            isRecording = true;
            printf("start recording video\n");
            std::string currTimeStr = CreateDirAndReturnCurrTimeStr("/home/rpdzkj/wjm/videos_recorded");
            std::string saveVideoFileName = "/home/rpdzkj/wjm/videos_recorded/" + currTimeStr + ".mp4";
            if (writer == nullptr)
            {

                writer = new cv::VideoWriter();
            }
            std::string pipeline = "appsrc ! videoconvert ! video/x-raw,format=I420 ! queue max-size-buffers=0 max-size-bytes=0 max-size-time=1000000000 ! x264enc ! h264parse ! mp4mux ! filesink location=" + saveVideoFileName;
            writer->open(pipeline, cv::CAP_GSTREAMER, 0, 30, cv::Size(1280, 720), true);
            if (writer->isOpened())
            {
                printf("writer open success\n");
            }
            else
            {
                printf("writer open failed\n");
            }
        }
        else if (stSysStatus.enScreenOpMode == EN_SCREEN_OP_MODE::RECORDING_END && isRecording)
        {
            stSysStatus.enScreenOpMode = EN_SCREEN_OP_MODE::SCREEN_NONE;
            printf("recording end\n");
            isRecording = false;
        }

        if (stSysStatus.detOn)
        {
            {
                std::unique_lock<std::mutex> lock(detectAndTrackMtx);
                detRet = g_detRet;
            }

            for (auto &box : detRet)
            {
                // 假设box对象有一个obj_id成员
                size_t colorIndex = box.obj_id % predefinedColors.size();
                cv::Scalar color = predefinedColors[colorIndex];

                cv::rectangle(frameQueue.front(), cv::Point(box.x, box.y), cv::Point(box.x + box.w, box.y + box.h), color, 2, 8);

                // 在框的左上角添加obj_id文本
                std::string id_text = std::to_string(box.obj_id);
                cv::putText(frameQueue.front(), id_text, cv::Point(box.x, box.y), cv::FONT_HERSHEY_SIMPLEX, 1, color, 2);
            }

            // for (auto &box : detRet)
            // {
            //         cv::rectangle(frameQueue.front(), cv::Point(box.x, box.y), cv::Point(box.x + box.w, box.y + box.h), cv::Scalar(0, 255, 255), 2, 8);
            // }
        }
        if (stSysStatus.trackOn)
        {
            {

                std::unique_lock<std::mutex> lock(trackMtx);
                cv::rectangle(frameQueue.front(), g_trackRect, cv::Scalar(255, 255, 255), 3, 8);
            }
        }

        {
            std::unique_lock<std::mutex> lock(OSDMtx);
            OSDFrame = frameQueue.front().clone();
            OSDconVar.notify_one();
        }

        nFrames++;
        {
            std::unique_lock<std::mutex> lock(frameMtx);
            frameQueue.pop();
        }

        if (nFrames % 60 == 0)
        {
            gettimeofday(&time, nullptr);
            tmpTime = time.tv_sec * 1000 + time.tv_usec / 1000;
            printf("<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<60帧平均帧率:\t%f帧\n", 60000.0 / (float)(tmpTime - lopTime));
            lopTime = tmpTime;
        }
    }

    cv::waitKey(100);
    rtspWriterr.release();
    return 0;
}

void serialViewLinkFunc()
{
    uint8_t output[1024] = {0};
    int outLen = 0;
    uint8_t buffRcvData[1024] = {0};
    int retLen = 0;

    std::vector<uint8_t> receiveBuffer;
    const std::vector<uint8_t> frameStart = {0x55, 0xAA, 0xDC};
    while (!interrupted.load())
    {
        retLen = serialViewLink.serial_receive(buffRcvData);
        if (retLen > 0)
        {
            // std::cout << "=======>serialUp received " << std::dec << retLen << "bytes" << std::endl;
            receiveBuffer.insert(receiveBuffer.end(), buffRcvData, buffRcvData + retLen);
            // 处理粘包的情况
            {
                // 循环直到缓冲区数据不够一帧的最小长度
                while (receiveBuffer.size() > frameStart.size())
                {
                    // 查找帧起始标志
                    auto frameStartIt = std::search(receiveBuffer.begin(), receiveBuffer.end(), frameStart.begin(), frameStart.end());
                    if (frameStartIt != receiveBuffer.end())
                    {
                        // 检查是否有足够的数据读取长度字节
                        auto headerEndIt = frameStartIt + frameStart.size();
                        if (std::distance(headerEndIt, receiveBuffer.end()) >= 1)
                        {
                            // 读取长度字节，假设长度字节紧随帧起始后
                            size_t frameLength = *(headerEndIt) & 0x3F; // 取字节的低6位作为长度
                            // std::cout<<frameLength<<std::endl;
                            // 检查是否有足够的数据包含整个帧
                            if (std::distance(headerEndIt, receiveBuffer.end()) >= frameLength)
                            {
                                // 提取帧，包括帧头和数据
                                std::vector<uint8_t> frame(frameStartIt, headerEndIt + frameLength);
                                // 处理帧

                                EN_DATA_FRAME_TYPE frameType = GetFrameType(frame, frameLength + 3);
                                // printf("frame type:%d\n", frameType);
                                if (frameType == HeartBeat15)
                                {
                                    printf("heart beat 15 from up serial\n\n");
                                    receiveBuffer.erase(receiveBuffer.begin(), headerEndIt + frameLength);
                                    continue;
                                }
                                else if (frameType == CtrlSdCmd)
                                {
                                    // printf("CtrlSdCmd from up serial\n\n");
                                    receiveBuffer.erase(receiveBuffer.begin(), headerEndIt + frameLength);
                                    continue;
                                }
                                else if (frameType == IPInq)
                                {
                                    // printf("IPInq from up serial\n\n");
                                    receiveBuffer.erase(receiveBuffer.begin(), headerEndIt + frameLength);
                                    continue;
                                }
                                else if (frameType == HandShake)
                                {
                                    printf("handshake from up serial\n\n");
                                    receiveBuffer.erase(receiveBuffer.begin(), headerEndIt + frameLength);
                                    continue;
                                }
                                else if (frameType == FrameS2)
                                {
                                    // printf("TGCC Ctrl S2 from up serial\n\n");
                                    receiveBuffer.erase(receiveBuffer.begin(), headerEndIt + frameLength);
                                    continue;
                                }
                                // else if (frameType == FrameE2)
                                // {
                                //     printf("TGCC Ctrl E2 from up serial\n\n");
                                //     receiveBuffer.erase(receiveBuffer.begin(), headerEndIt + frameLength);
                                //     continue;
                                // }
                                else if (frameType == Status42)
                                {
                                    // printf("TGCC Ctrl 42 from up serial\n\n");
                                    receiveBuffer.erase(receiveBuffer.begin(), headerEndIt + frameLength);
                                    continue;
                                }
                                else if (frameType == HeartBeat14)
                                {
                                    printf("heart beat 14 from up serial\n\n");
                                    receiveBuffer.erase(receiveBuffer.begin(), headerEndIt + frameLength);
                                    continue;
                                }
                                for (int i = 0; i < frame.size(); i++)
                                {
                                    printf("[%02X]", frame[i]);
                                }
                                printf("\n");
                                uint8_t *usefulFrame = frame.data();
                                VL_ParseSerialData(usefulFrame);

                                // 移除处理过的数据
                                receiveBuffer.erase(receiveBuffer.begin(), headerEndIt + frameLength);
                            }
                            else
                            {
                                // 不完整的帧，退出循环等待更多数据
                                break;
                            }
                        }
                        else
                        {
                            // 不完整的头，退出循环等待更多数据
                            break;
                        }
                    }
                    else
                    {
                        // 未找到帧起始标志，清空缓冲区
                        receiveBuffer.clear();
                        break;
                    }
                }
            }
        }
    }
}

// 序列化和反序列化函数
uint64_t serializeBytes(unsigned char *bytes)
{

    uint64_t value = 0;
    // std::cout<<std::hex<<bytes[0]<<bytes[1]<<bytes[2]<<bytes[3]<<std::endl;
    memcpy(&value, bytes, sizeof(uint32_t));
    return value;
}

void deserializeBytes(uint64_t value, unsigned char *bytes)
{
    memcpy(bytes, &value, sizeof(uint32_t));
}

uint32_t swapEndian(uint32_t value)
{
    uint32_t result = ((value & 0xFF000000) >> 24) |
                      ((value & 0x00FF0000) >> 8) |
                      ((value & 0x0000FF00) << 8) |
                      ((value & 0x000000FF) << 24);
    return result;
}

void serialSonyFunc()
{

    uint8_t buffRcvData[1024] = {0};
    int retLen = 0;
    std::vector<uint8_t> receiveBuffer;
    uint8_t zoom[10][4] = {
        {0x00, 0x00, 0x00, 0x00},
        {0x01, 0x06, 0x0C, 0x05},
        {0x02, 0x00, 0x08, 0x05},
        {0x02, 0x06, 0x04, 0x05},
        {0x02, 0x0A, 0x04, 0x05},
        {0x02, 0x0D, 0x04, 0x00},
        {0x02, 0x0F, 0x08, 0x00},
        {0x03, 0x01, 0x08, 0x00},
        {0x03, 0x03, 0x04, 0x00},
        {0x03, 0x04, 0x0C, 0x00}};
    while (!interrupted.load())
    {
        memset(buffRcvData, 0, sizeof(buffRcvData));
        retLen = serialRevSony.serial_receive(buffRcvData);
        bool found = false;

        if (retLen > 0)
        {
            for (int i = 0; i < retLen; i++)
            {
                printf("[%02X]", buffRcvData[i]);
            }
            // buffRcvData[retLen] = '\r';
            printf("\n");
            serialSendSony.serial_send(buffRcvData, retLen);

            for (int i = 0; i < 10; ++i)
            { // 遍历 zoom 数组的每一行
                if (zoom[i][0] == buffRcvData[4] &&
                    zoom[i][1] == buffRcvData[5] &&
                    zoom[i][2] == buffRcvData[6] &&
                    zoom[i][3] == buffRcvData[7])
                {
                    std::this_thread::sleep_for(std::chrono::milliseconds(500));
                    zoomFlag = true;
                    std::cout << "Matching index in zoom array: " << i << std::endl;
                    zoomGrade = i + 1;
                    break; // 匹配后退出循环
                }
            }
        }
    }
}

void SaveRecordVideoFunc()
{
    cv::Mat mat;
    while (!interrupted.load())
    {
        if (isRecording)
        {
            auto start = std::chrono::high_resolution_clock::now();
            if (writer != nullptr)
            {
                std::unique_lock<std::mutex> lock(m_mtx);
                writer->write(saveFrame);
            }
            std::this_thread::sleep_for(std::chrono::milliseconds(30));

            auto end = std::chrono::high_resolution_clock::now();

            // 计算线程的运行时间，单位为毫秒
            auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
            std::cout << "save video single-frame time: " << std::dec << duration.count() << " ms" << std::endl;
        }
        if (!isRecording && writer != nullptr)
        {
            writer->release();
            writer = nullptr;
        }
    }
}
