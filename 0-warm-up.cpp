#include <iostream>
#include <fstream>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>
#include <semaphore.h>
#include <arm_neon.h>
using namespace std;
string trainFile = "/data/train_data.txt";
string testFile = "/data/test_data.txt";
string predictFile = "/projects/student/result.txt";
string answerFile = "/projects/student/answer.txt";
#define train_size 3200
#define test_size 20000
#define test_size_gap 3600
#define feature_size 1000
#define used_feature_size 992
#define used_feature_size2 1
#define train_char_line 7002
#define test_char_line 6000
inline void* create_shared_memory(size_t size) {
    int protection = PROT_READ | PROT_WRITE;
    int visibility = MAP_SHARED | MAP_ANONYMOUS;
    return mmap(NULL, size, protection, visibility, -1, 0);
}
struct shared{
    char test_label[test_size*2+1];
    int feature_sum0[4][used_feature_size];
    int feature_sum1[4][used_feature_size];
    int mean_cnt[4][2];
};
shared* shm;
char* train_char;
char* test_char;
inline void arm_neon_add(int* x, int* y, int sz){
    int32x4_t sum_vec,left_vec,right_vec;
    for(int i=0;i<sz;i+=4){
        left_vec = vld1q_s32(x+i);
        right_vec = vld1q_s32(y+i);
        sum_vec = vaddq_s32(left_vec, right_vec);
        vst1q_s32(x + i, sum_vec);
    }
}
void load_train_data(){
    int fd1 = open(trainFile.c_str(), O_RDONLY);
    int len1 = 20128602;//(train_size/4*3)*(test_char_line+50)+(train_size-train_size/4*3+1)*train_char_line;
    train_char = (char*)mmap(NULL, len1, PROT_READ, MAP_PRIVATE, fd1, 0);
    close(fd1);
}
void read_train_data_td(int id, int st,int ed){
    int chcnt = st*(test_char_line+50);
    if(chcnt!=0)
        for(int i=0;i<train_char_line;i++){
            if(train_char[chcnt]!='\n')
                chcnt++;
            else break;
        }
    chcnt++;
    int cnt0=0,cnt1=0;
    int sum1 = 0;
    int train_data[used_feature_size];
    for(int i=st;i<ed;i++){
        int sum2=0;
        char* buff = train_char + chcnt + sum1;
        for(int j=0;j<used_feature_size;j+=16){
            for(int k=0;k<16;k++){
                if(buff[0+sum2]=='-'){
                    train_data[j+k] = -100*(buff[3+sum2]-'0');
                    //val = -(1000*(buff[1+sum2]-'0') + 100*(buff[3+sum2]-'0') + 10*(buff[4+sum2]-'0') + (buff[5+sum2]-'0')  );
                    sum2 += 7;
                }
                else{
                    train_data[j+k] = 100*(buff[2+sum2]-'0');
                    //val = 1000*(buff[0+sum2]-'0') + 100*(buff[2+sum2]-'0') + 10*(buff[3+sum2]-'0') + (buff[4+sum2]-'0');
                    sum2 += 6;
                }
            }
        }
        for(int j=0;j<feature_size-used_feature_size;j++){
                sum2 += (buff[0+sum2]=='-'?7:6);
        }
        if(buff[0+sum2]-'0'){
            cnt1++;
            arm_neon_add(shm->feature_sum1[id], train_data, used_feature_size);
        }
        else{
            cnt0++;
            arm_neon_add(shm->feature_sum0[id], train_data, used_feature_size);
        }
        sum2 += 2;
        sum1 += sum2;
    }
    shm->mean_cnt[id][0] = cnt0;
    shm->mean_cnt[id][1] = cnt1;
}
void load_test_data(){
    int fd2 = open(testFile.c_str(), O_RDONLY);
    int len2 = (int)lseek(fd2, 0, SEEK_END);
    test_char = (char*)mmap(NULL, len2, PROT_READ, MAP_PRIVATE, fd2, 0);
    close(fd2);
}
void read_test_data_td(int st, int ed){
    int test_data[16];
    for(int i=0;i<ed-st;i++){
        char* sub_test_char = test_char + (st+i) * 6000;
        int32x4_t sum0_vec = vdupq_n_s32(0),sum1_vec = vdupq_n_s32(0);
        int32x4_t left_vec,right_vec;
        for(int j=0;j<used_feature_size;j+=16){
            char* buff = sub_test_char + j*6;
            for(int k=0;k<16;k++){
                test_data[k] = 100*(buff[2+k*6]-'0');
                //test_data[k] = 1000*(buff[0+k*6]-'0') + 100*(buff[2+k*6]-'0') + 10*(buff[3+k*6]-'0') + 1*(buff[4+k*6]-'0');
            }
            for(int k=0;k<16;k+=4){
                left_vec = vld1q_s32(test_data+k);
                right_vec = vld1q_s32(shm->feature_sum0[0]+j+k);
                right_vec = vsubq_s32(left_vec, right_vec);
                sum0_vec = vmlaq_s32(sum0_vec, right_vec, right_vec);
                right_vec = vld1q_s32(shm->feature_sum1[0]+j+k);
                right_vec = vsubq_s32(left_vec, right_vec);
                sum1_vec = vmlaq_s32(sum1_vec, right_vec, right_vec);
            }
        }
        int32x2_t r0 = vadd_s32(vget_high_s32(sum0_vec), vget_low_s32(sum0_vec));
        int dis0 = vget_lane_s32(vpadd_s32(r0, r0), 0);
        int32x2_t r1 = vadd_s32(vget_high_s32(sum1_vec), vget_low_s32(sum1_vec));
        int dis1 = vget_lane_s32(vpadd_s32(r1, r1), 0);
        shm->test_label[(st+i)*2] = (dis0<dis1?0:1)+'0';
        shm->test_label[(st+i)*2+1] = '\n';
    }
}
void read_test_data_td2(int st,int ed){
    int line_size = feature_size*6;
    for(int i=st;i<ed;i++){
        char* buff = test_char+i*line_size;
        shm->test_label[i*2] = ((buff[0]-'0'>=0)?1:0)+'0';
        shm->test_label[i*2+1] = '\n';
    }
}
void calculate_mean(){
    int cnt0=0,cnt1=0;
    for(int i=0;i<4;i++){
        cnt0+=shm->mean_cnt[i][0];
        cnt1+=shm->mean_cnt[i][1];
    }
    arm_neon_add(shm->feature_sum0[0], shm->feature_sum0[1], used_feature_size);
    arm_neon_add(shm->feature_sum0[2], shm->feature_sum0[3], used_feature_size);
    arm_neon_add(shm->feature_sum0[0], shm->feature_sum0[2], used_feature_size);
    arm_neon_add(shm->feature_sum1[0], shm->feature_sum1[1], used_feature_size);
    arm_neon_add(shm->feature_sum1[2], shm->feature_sum1[3], used_feature_size);
    arm_neon_add(shm->feature_sum1[0], shm->feature_sum1[2], used_feature_size);
    for(int i=0;i<used_feature_size;i++)
        shm->feature_sum0[0][i]/=cnt0;
    for(int i=0;i<used_feature_size;i++)
        shm->feature_sum1[0][i]/=cnt1;
}
void save_result(){
    shm->test_label[test_size*2] = '\0';
    ofstream resultWrite(predictFile);
    resultWrite<<shm->test_label;
    resultWrite.close();
}
void evaluate(){
    int fd = open(answerFile.c_str(), O_RDONLY);
    int len = (int)lseek(fd, 0, SEEK_END);
    char* file = (char*)mmap(NULL, len, PROT_READ, MAP_PRIVATE, fd, 0);
    int accCnt = 0;
    int tolCnt = 0;
    for(int i=0;i<test_size;i++){
        tolCnt++;
        if((file[i*2]-'0')==(shm->test_label[i*2]-'0')){
            accCnt++;
        }
    }
    cout<<"准确率: "<<(accCnt*1.0/tolCnt)*100<<"%"<<endl;
}
int main(){
    sem_t* psem[4];
    for(int i=0;i<4;i++){
        psem[i] = (sem_t*)create_shared_memory(sizeof(sem_t));//(sem_t*)mmap(NULL,sizeof(sem_t),PROT_READ|PROT_WRITE,MAP_SHARED,-1,0);
        sem_init(psem[i],1,0);
    }
    shm = (struct shared*)create_shared_memory(sizeof(struct shared));
    load_train_data();
    load_test_data();
    int pid1=-1,pid2=-1,pid3=-1;
    pid1=fork();
    if(pid1!=0) pid2 = fork();
    if(pid1!=0&&pid2!=0) pid3 = fork();
    if(pid1==0){
        read_train_data_td(1, train_size/4, train_size/2);
        sem_post(psem[1]);
        sem_wait(psem[0]);
        read_test_data_td(test_size_gap/4, test_size_gap/2);
        read_test_data_td2(test_size_gap+(test_size-test_size_gap)/4, test_size_gap+(test_size-test_size_gap)/2);
        sem_post(psem[1]);
    }
    else if(pid2==0){
        read_train_data_td(2, train_size/2, train_size/4*3);
        sem_post(psem[2]);
        sem_wait(psem[0]);
        read_test_data_td(test_size_gap/2, test_size_gap/4*3);
        read_test_data_td2(test_size_gap+(test_size-test_size_gap)/2, test_size_gap+(test_size-test_size_gap)/4*3);
        sem_post(psem[2]);
    }
    else if(pid3==0){
        read_train_data_td(3, train_size/4*3, train_size);
        sem_post(psem[3]);
        sem_wait(psem[0]);
        read_test_data_td(test_size_gap/4*3, test_size_gap);
        read_test_data_td2(test_size_gap+(test_size-test_size_gap)/4*3, test_size_gap+(test_size-test_size_gap));
        sem_post(psem[3]);
    }
    else{
        read_train_data_td(0, 0, train_size/4);
        sem_wait(psem[1]);
        sem_wait(psem[2]);
        sem_wait(psem[3]);
        calculate_mean();
        sem_post(psem[0]);
        sem_post(psem[0]);
        sem_post(psem[0]);
        read_test_data_td(0, test_size_gap/4);
        read_test_data_td2(test_size_gap, test_size_gap+(test_size-test_size_gap)/4);
        sem_wait(psem[1]);
        sem_wait(psem[2]);
        sem_wait(psem[3]);
        save_result();
        //evaluate();
    }
    return 0;
}
