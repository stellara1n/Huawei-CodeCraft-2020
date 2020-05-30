#include <iostream>
#include <algorithm>
#include <fstream>
#include <cstring>
#include <unordered_set>
#include <unordered_map>
#include <fcntl.h>
#include <sys/mman.h>
#include <thread>
#include <mutex>
#include <sys/time.h>
#include <unistd.h>
#include <type_traits>
#include <limits>
#include <future>
using namespace std;
string testFile = "./data/test_data.txt";
string resultFile = "./projects/student/result.txt";
#define MAXI 560000
#define MAXV 560005
#define MAXE 280005
#define STEP 10

#define FORCE_INLINE static inline __attribute__((always_inline))
struct gg { char t, o; };
#define P(T) T, '0',  T, '1', T, '2', T, '3', T, '4', T, '5', T, '6', T, '7', T, '8', T, '9'
static const gg s_pairs[] = { P('0'), P('1'), P('2'), P('3'), P('4'), P('5'), P('6'), P('7'), P('8'), P('9') };
#define W(N, I) *(gg*)&b[N] = s_pairs[I]
#define A(N) t = (uint64_t(1) << (32 + N / 5 * N * 53 / 16)) / uint32_t(1e##N) + 1 + N/6 - N/8, t *= u, t >>= N / 5 * N * 53 / 16, t += N / 6 * 4, W(0, t >> 32)
#define S(N) b[N] = char(uint64_t(10) * uint32_t(t) >> 32) + '0'
#define D(N) t = uint64_t(100) * uint32_t(t), W(N, t >> 32)

#define L0 b[0] = char(u) + '0'
#define L1 W(0, u)
#define L2 A(1), S(2)
#define L3 A(2), D(2)
#define L4 A(3), D(2), S(4)
#define L5 A(4), D(2), D(4)
#define L6 A(5), D(2), D(4), S(6)
#define LN(N) (L##N, b += N + 1)
#define LZ(N) (L##N, length = N)
#define LG(F) (u<100 ? u<10 ? F(0) : F(1) :u<10000 ? u<1000 ? F(2) : F(3) : F(4))
FORCE_INLINE int u32toa_jeaiii(uint32_t u, char* b)
{
    int length;
    uint64_t t;
    LG(LZ);
    return length+1;
}

template <typename IntegerType>
void multi_threaded_sort(IntegerType* in_data, size_t data_len, size_t thread_num)
{
    if(data_len <= 1 || thread_num == 0 || data_len < (thread_num+1)*(thread_num+1)){
        sort(in_data, in_data+data_len);
        return;
    }
    size_t chunk_size = data_len/(thread_num+1);
    if(data_len%(thread_num+1) != 0)
        ++chunk_size;
    auto sort_promise = new promise<void>[thread_num];
    auto sort_future = new future<void>[thread_num];
    for(int i=0; i<thread_num; ++i)
        sort_future[i] = sort_promise[i].get_future();
    for(size_t i=0; i<thread_num; ++i){
        thread th([=]{
            sort(in_data + i*chunk_size, in_data + (i+1)*chunk_size);
            sort_promise[i].set_value();
        });
        th.detach();
    }
    sort(in_data + chunk_size*thread_num, in_data + data_len);
    // before wait and block, do things not based on data
    auto out_data = new IntegerType[data_len];
    auto index = new size_t[thread_num + 1];
    for (int i=0; i<thread_num + 1; ++i)
        index[i] = i * chunk_size;
    
    // wait for all threads
    for(size_t i=0; i<thread_num; ++i)
        sort_future[i].wait();
    delete[] sort_future;
    delete[] sort_promise;
    
    // do merge sort
    for(size_t i = 0; i < data_len; ++i)
    {
        IntegerType min_index;
        IntegerType min_num = numeric_limits<IntegerType>::max();
        
        // traverse every chunk and find the minimum
        for(size_t j=0; j<thread_num; ++j)
        {
            if((index[j] < (j+1)*chunk_size)
               && (in_data[index[j]] < min_num))
            {
                min_index = j;
                min_num = in_data[index[j]];
            }
        }
        if(index[thread_num] < data_len
           && (in_data[index[thread_num]] < min_num))
        {
            min_index = thread_num;
        }
        
        out_data[i] = in_data[index[min_index]];
        index[min_index]++;
    }
    memcpy(in_data, out_data, sizeof(IntegerType)*data_len);
    delete[] out_data;
}

inline uint64_t EDGE(int x,int y){return (uint64_t)(uint64_t(x) <<32u | uint64_t(y));}
inline int FROM(uint64_t x){return int(uint64_t(x) >> 32u);}
inline int TO(uint64_t x){return int(x);}
struct Stack{int s[MAXV],top;inline void clr(){top=0;}inline bool emp(){return !(top);}inline void push(int x){s[top++]=x;}inline int pop(){return s[--top];}};

mutex mtx;int mtx_num=0;
int v_total;
int e_total;
int scc_total;
int ans_total;
int max_id;
int index2id[MAXV];
uint64_t edges[MAXE],redges[MAXE];

int neb[30005][50];
int rneb[30005][50];
Stack s1,s2;
bool visit_e[MAXE];
bool visit_v[4][MAXV];
int que[4][MAXV];

int low[4][MAXV],dfn[4][MAXV];
int ans_tid[MAXV];
int ans_tid_cnt[5][MAXV];
char* ans_str[4];
int ans_str_len[4];
int* ans_ptr[4][5];
int ans_cnt[4][5];
int* ans_sort[4000000];
int ans[4][5][32000000];
void read(){
    int fd = open(testFile.c_str(), O_RDONLY);
    int test_char_size = (int)lseek(fd, 0, SEEK_END);
    char* test_char = (char*)mmap(NULL, test_char_size, PROT_READ, MAP_PRIVATE, fd, 0);
    
    max_id = -1;
    int e_cnt = 0;
    int from = 0,to = 0;
    char* pt=test_char;
    char* ed = test_char + test_char_size;
    while(pt<ed){
        from = to = 0;
        while(*pt!=','){
            from = from*10 + *pt-'0';
            pt++;
        }
        pt++;
        while(*pt!=','){
            to = to*10 + *pt-'0';
            pt++;
        }
        pt++;
        while(*pt!='\n'){
            pt++;
        }
        pt++;
        max_id = max(max(max_id,from),to);
        edges[e_cnt] = EDGE(from,to);
        e_cnt++;
    }
    e_total = e_cnt;
    v_total = max_id + 1;
    
    if(max_id>MAXI){
        unordered_map<int, int> id2index;
        memcpy(index2id, edges, e_total * sizeof(int64_t));
        multi_threaded_sort(index2id, e_total * 2, 3);
        int index = 0;
        id2index[index2id[0]] = index;
        index2id[index] = index2id[0];
        index++;
        for(int i=1;i<e_total*2;i++){
            if(index2id[i-1]==index2id[i])continue;
            id2index[index2id[i]] = index;
            index2id[index] = index2id[i];
            index++;
        }
        v_total = index;
        for(int i=0;i<v_total;i++){
            id2index[index2id[i]] = i;
        }
        for(int i=0;i<e_total;i++){
            edges[i] = EDGE(id2index[FROM(edges[i])], id2index[TO(edges[i])]);
        }
    }
    for(int i=0;i<e_total;i++){
        redges[i] = EDGE(TO(edges[i]), FROM(edges[i]));
    }
    multi_threaded_sort(edges,e_total,3);
    multi_threaded_sort(redges,e_total,3);
    for(int i=0;i<v_total;i++){
        neb[i][0] = 0;
        rneb[i][0] = 0;
    }
    for(int i=0;i<e_total;i++){
        from = FROM(edges[i]);
        to = TO(edges[i]);
        neb[from][++neb[from][0]] = to;
    }
    for(int i=0;i<e_total;i++){
        from = FROM(redges[i]);
        to = TO(redges[i]);
        rneb[from][++rneb[from][0]] = to;
    }
    
}

void bfs(int tid, int s){
    int cnt0=0,cnt1=0,u,v;
    dfn[tid][s] = 0;
    low[tid][s] = s;
    u = s;
    for(int* i=lower_bound(rneb[s]+1, rneb[s]+1+rneb[s][0], s);i<rneb[s]+1+rneb[s][0];i++){
        v = *i;
        if(low[tid][v]==s)continue;
        low[tid][v]=s;
        dfn[tid][v]=1;
        que[tid][cnt0++] = v;
    }
    cnt1 = cnt0;
    for(int j=0;j<cnt0;j++){
        u = que[tid][j];
        for(int* i=lower_bound(rneb[u]+1, rneb[u]+1+rneb[u][0], s);i<rneb[u]+1+rneb[u][0];i++){
            v = *i;
            if(low[tid][v]==s)continue;
            low[tid][v]=s;
            dfn[tid][v]=2;
            que[tid][cnt1++] = v;
        }
    }
    for(int j=cnt0;j<cnt1;j++){
        u = que[tid][j];
        for(int* i=lower_bound(rneb[u]+1, rneb[u]+1+rneb[u][0], s);i<rneb[u]+1+rneb[u][0];i++){
            v = *i;
            if(low[tid][v]==s)continue;
            low[tid][v]=s;
            dfn[tid][v]=3;
        }
    }
}
void dfs7(int tid, int s){
    int* ans_ptr_old[5];
    for(int i=0;i<5;i++)
        ans_ptr_old[i] = ans_ptr[tid][i];
    int v1,v2,v3,v4,v5,v6;
    int stk[8];
    stk[0] = s;
    visit_v[tid][s] = true;
    for(int* i1=lower_bound(neb[s]+1, neb[s]+1+neb[s][0], s);i1<neb[s]+1+neb[s][0];i1++){
        v1 = *i1;
        stk[1] = v1;
        visit_v[tid][v1] = true;
        for(int* i2=lower_bound(neb[v1]+1, neb[v1]+1+neb[v1][0], s);i2<neb[v1]+1+neb[v1][0];i2++){
            v2 = *i2;
            if(visit_v[tid][v2])continue;
            stk[2] = v2;
            visit_v[tid][v2] = true;
            for(int* i3=lower_bound(neb[v2]+1, neb[v2]+1+neb[v2][0], s);i3<neb[v2]+1+neb[v2][0];i3++){
                v3 = *i3;
                if(v3==s){
                    ans_ptr[tid][0][0] = 3;
                    for(int k=0;k<3;k++){
                        ans_ptr[tid][0][k+1] = stk[k];
                    }
                    ans_ptr[tid][0]+=8;
                    continue;
                }
                if(visit_v[tid][v3])continue;
                stk[3] = v3;
                visit_v[tid][v3] = true;
                for(int* i4=lower_bound(neb[v3]+1, neb[v3]+1+neb[v3][0], s);i4<neb[v3]+1+neb[v3][0];i4++){
                    v4 = *i4;
                    if(v4==s){
                        ans_ptr[tid][1][0] = 4;
                        for(int k=0;k<4;k++){
                            ans_ptr[tid][1][k+1] = stk[k];
                        }
                        ans_ptr[tid][1]+=8;
                        continue;
                    }
                    if(low[tid][v4]!=s||visit_v[tid][v4])continue;
                    stk[4] = v4;
                    visit_v[tid][v4] = true;
                    for(int* i5=lower_bound(neb[v4]+1, neb[v4]+1+neb[v4][0], s);i5<neb[v4]+1+neb[v4][0];i5++){
                        v5 = *i5;
                        if(v5==s){
                            ans_ptr[tid][2][0] = 5;
                            for(int k=0;k<5;k++){
                                ans_ptr[tid][2][k+1] = stk[k];
                            }
                            ans_ptr[tid][2]+=8;
                            continue;
                        }
                        if(low[tid][v5]!=s||dfn[tid][v5]>2||visit_v[tid][v5])continue;
                        stk[5] = v5;
                        visit_v[tid][v5] = true;
                        for(int* i6=lower_bound(neb[v5]+1, neb[v5]+1+neb[v5][0], s);i6<neb[v5]+1+neb[v5][0];i6++){
                            v6 = *i6;
                            if(v6==s){
                                ans_ptr[tid][3][0] = 6;
                                for(int k=0;k<6;k++){
                                    ans_ptr[tid][3][k+1] = stk[k];
                                }
                                ans_ptr[tid][3]+=8;
                                continue;
                            }
                            if(low[tid][v6]!=s||dfn[tid][v6]>1||visit_v[tid][v6])continue;
                            stk[6] = v6;
                            visit_v[tid][v6] = true;
                            int *i7 = lower_bound(neb[v6]+1, neb[v6]+1+neb[v6][0], s);
                            if(i7<neb[v6]+1+neb[v6][0]&&*i7==s){
                                ans_ptr[tid][4][0] = 7;
                                for(int k=0;k<7;k++){
                                    ans_ptr[tid][4][k+1] = stk[k];
                                }
                                ans_ptr[tid][4]+=8;
                            }
                            visit_v[tid][v6] = false;
                        }
                        visit_v[tid][v5] = false;
                    }
                    visit_v[tid][v4] = false;
                }
                visit_v[tid][v3] = false;
            }
            visit_v[tid][v2] = false;
        }
        visit_v[tid][v1] = false;
    }
    visit_v[tid][s] = false;
    for(int i=0;i<5;i++)
        ans_tid_cnt[i][s] += (int)(ans_ptr[tid][i]-ans_ptr_old[i])/8;
}
void search_mt(int tid){
    for(int i=0;i<5;i++)
        ans_ptr[tid][i] = &ans[tid][i][0];
    memset(low[tid],-1,sizeof(int)*v_total);
    memset(visit_v[tid],false,sizeof(bool)*v_total);
    int u;
    int st,ed;
    while(true){
        mtx.lock();
        u = mtx_num++;
        mtx.unlock();
        st = u*STEP;
        if(st>=v_total)break;
        ans_tid[u] = tid;
        ed = min(st+STEP,v_total);
        for(int i=st;i<ed;i++){
            bfs(tid,i);
            dfs7(tid,i);
        }
    }
}
void search(){
    memset(ans_tid,-1,sizeof(int)*v_total);
    for(int i=0;i<5;i++)
        memset(ans_tid_cnt[i],0,sizeof(int)*v_total);
    thread td[3];
    for(int i=0;i<3;i++){
        td[i] = thread(search_mt,i);
    }
    search_mt(3);
    for(int i=0;i<3;i++)td[i].join();
    ans_total=0;
    for(int k=0;k<4;k++)
    for(int i=0;i<5;i++){
        ans_cnt[k][i] = (int)(ans_ptr[k][i]-ans[k][i])/8;
        ans_total += ans_cnt[k][i];
    }
    cout<<"answer:"<<ans_total<<endl;
}
void merge(){
    int* ans_ptr_now[4][5];
    for(int i=0;i<4;i++){
        for(int j=0;j<5;j++)
            ans_ptr_now[i][j] = &ans[i][j][0];
    }
    int cnt=0;
    for(int k=0;k<5;k++){
        for(int i=0;i<v_total;i++){
            int tid = ans_tid[i/STEP];
            for(int r=0;r<ans_tid_cnt[k][i];r++){
                ans_sort[cnt++] = ans_ptr_now[tid][k];
                ans_ptr_now[tid][k] += 8;
            }
        }
    }
}
void trans_mt(int tid, int st, int ed){
    
    if(max_id>MAXI){
        for(int i=st;i<ed;i++){
            int len = ans_sort[i][0];
            for(int j=1;j<=len;j++){
                ans_sort[i][j] = index2id[ans_sort[i][j]];
            }
        }
    }
    ans_str[tid] = new char[80*(ed-st)+10];
    int char_cnt = 0;
    if(tid==0){
        char_cnt += snprintf(ans_str[tid], 10 , "%d", ans_total);
        ans_str[tid][char_cnt++] = '\n';
    }
    for(int i=st;i<ed;i++){
        int len = ans_sort[i][0];
        char_cnt += u32toa_jeaiii(ans_sort[i][1], ans_str[tid] + char_cnt);
        for(int j=2;j<=len;j++){
            ans_str[tid][char_cnt++] = ',';
            char_cnt += u32toa_jeaiii(ans_sort[i][j], ans_str[tid] + char_cnt);
        }
        ans_str[tid][char_cnt++] = '\n';
    }
    ans_str_len[tid] = char_cnt;
    ans_str[tid][char_cnt++] = '\0';
}
void trans(){
    int cnt[5];
    int avg = 0;
    for(int i=0;i<5;i++){
        cnt[i] = 0;
        for(int j=0;j<4;j++)
            cnt[i]+=ans_cnt[j][i];
        avg+=(i+5)*cnt[i];
    }
    avg/=4;
    int st[4],ed[4];
    int now = 0;
    for(int i=0;i<4;i++){
        st[i] = now;
        int ext = avg;
        for(int j=0;j<5;j++){
            if(cnt[j]==0)continue;
            if(cnt[j]*(j+5)<=ext){
                ext -= cnt[j]*(j+5);
                now += cnt[j];
                cnt[j]=0;
            }
            else{
                now += ext/(j+5);
                cnt[j] -= ext/(j+5);
                ext = 0;
            }
        }
        ed[i] = now;
    }
    ed[3] = ans_total;
    thread td[3];
    for(int i=0;i<3;i++){
        td[i] = thread(trans_mt,i,st[i],ed[i]);
    }
    trans_mt(3,st[3],ed[3]);
    for(int i=0;i<3;i++)td[i].join();
}
void save(){
    /*timeval t_start, t_end;
    gettimeofday( &t_start, NULL);
    gettimeofday( &t_end, NULL);
    double delta_t = (t_end.tv_sec-t_start.tv_sec) + (t_end.tv_usec-t_start.tv_usec)/1000000.0;
    cout<<"save:"<<delta_t<<"s"<<endl;*/
    //this_thread::sleep_for(chrono::milliseconds(int(delta_t*10000)));
    int fd = open(resultFile.c_str(), O_RDWR | O_CREAT, 0666);
    for(int i=0;i<4;i++) write(fd, ans_str[i], ans_str_len[i]);
    close(fd);
    for(int i=0;i<4;i++) delete []ans_str[i];
}
int main(){
    read();
    //tarjan();
    search();
    merge();
    trans();
    save();
    return 0;
}
