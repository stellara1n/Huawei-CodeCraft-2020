#include <iostream>
#include <algorithm>
#include <cstring>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <unistd.h>
#include <thread>
#include <stdio.h>
#include <atomic>
#include <unordered_map>
using namespace std;
string testFile = "/data/test_data.txt";
//string testFile = "./data/test_data.N111314.E200W.A19630345.txt";
string resultFile = "/projects/student/result.txt";
#define MAXP 4000000//2097152*2
#define MAXE 2000005//2097152
#define MAXV 8000005//4194304*2
#define MAXA 20000005
typedef long long ll;
int v_total;
int e_total;
int scc_total;
int ans_total;
bool mapped = false;
int valid_total;
int valid_v[MAXV];
int index2id[MAXV];
struct Edge{
    int from,to;
    ll value;
    inline void set(int _from, int _to, ll _value){
        from = _from;
        to = _to;
        value = _value;
    };
    bool operator < (const Edge & e) const {
        return from==e.from?(to<e.to):(from<e.from);
    }
}edges[MAXE],redges[MAXE];

int too[MAXE],rtoo[MAXE];
ll val[MAXE],rval[MAXE];
int flg[MAXV],rflg[MAXV];
bool visit[MAXV];
atomic<int> mtx_num(0);

struct Back{
    int s[4];
    ll a,b;
    int nxt;
    inline void set(int x, int y, int z, int w, ll aa, ll bb, int nnn){
        s[0] = x;
        s[1] = y;
        s[2] = z;
        s[3] = w;
        a = aa;
        b = bb;
        nxt = nnn;
    }
    bool operator < (const Back & b) const {
        return s[1]==b.s[1]?(s[2]==b.s[2]?s[3]<b.s[3]:s[2]<b.s[2]):s[1]<b.s[1];
    }
}*back[4],*back_sort[4];
int back_cnt[4][32];
int back_sort_cnt[4][32];
bool update[4][MAXV];
bool sorted[4][MAXV];
int head[4][MAXV];
int back_idx[4][MAXV*2];

int ans_v_cnt[MAXV*32];
int ans_cnt[4][32];
struct Ans{
    int len;
    int num[8];
};
Ans* ans[4][6];
Ans** ans_sorted;
char* ans_out[4];
int ans_out_len[4][32];

#define FORCE_INLINE static inline __attribute__((always_inline))
static const uint16_t s_100s[] = {
    12336,12592,12848,13104,13360,13616,13872,14128,14384,14640,
    12337,12593,12849,13105,13361,13617,13873,14129,14385,14641,
    12338,12594,12850,13106,13362,13618,13874,14130,14386,14642,
    12339,12595,12851,13107,13363,13619,13875,14131,14387,14643,
    12340,12596,12852,13108,13364,13620,13876,14132,14388,14644,
    12341,12597,12853,13109,13365,13621,13877,14133,14389,14645,
    12342,12598,12854,13110,13366,13622,13878,14134,14390,14646,
    12343,12599,12855,13111,13367,13623,13879,14135,14391,14647,
    12344,12600,12856,13112,13368,13624,13880,14136,14392,14648,
    12345,12601,12857,13113,13369,13625,13881,14137,14393,14649,
};
#define A(N) t = (1ULL << (32 + N / 5 * N * 53 / 16)) / uint32_t(1e##N) + 1 - N / 9, t *= u, t >>= N / 5 * N * 53 / 16, t += N / 5 * 4
#define W(N, I) *(uint16_t*)&b[N] = s_100s[I]
#define Q(N) b[N] = char((10ULL * uint32_t(t)) >> 32) + '0'
#define D(N) W(N, t >> 32)
#define E t = 100ULL * uint32_t(t)
#define L0 b[0] = char(u) + '0'
#define L1 W(0, u)
#define L2 A(1), D(0), Q(2)
#define L3 A(2), D(0), E, D(2)
#define L4 A(3), D(0), E, D(2), Q(4)
#define L5 A(4), D(0), E, D(2), E, D(4)
#define L6 A(5), D(0), E, D(2), E, D(4), Q(6)
#define L7 A(6), D(0), E, D(2), E, D(4), E, D(6)
#define L8 A(7), D(0), E, D(2), E, D(4), E, D(6), Q(8)
#define L9 A(8), D(0), E, D(2), E, D(4), E, D(6), E, D(8)
#define LN(N) (L##N, b += N + 1)
#define LZ(N) (L##N, length = N)
#define LG(F) (u<100 ? u<10 ? F(0) : F(1) : u<1000000 ? u<10000 ? u<1000 ? F(2) : F(3) : u<100000 ? F(4) : F(5) : u<100000000 ? u<10000000 ? F(6) : F(7) : u<1000000000 ? F(8) : F(9))
FORCE_INLINE int u32toa_jeaiii(uint32_t u, char* b){
    uint8_t length;
    uint64_t t;
    LG(LZ);
    return length+1;
}
void mt_sort_int(int* in_data, int data_len, int thread_num){
    if(data_len<=1||thread_num==0||data_len<(thread_num+1)*(thread_num+1)){
        sort(in_data, in_data+data_len);
        return;
    }
    int chunk_size = data_len/(thread_num+1);
    if(data_len%(thread_num+1) != 0)
        ++chunk_size;
    thread td[thread_num];
    for(int i=0; i<thread_num; ++i){
        td[i] = thread([=]{
            sort(in_data + i*chunk_size, in_data + (i+1)*chunk_size);
        });
    }
    sort(in_data + chunk_size*thread_num, in_data + data_len);
    int* out_data = new int[data_len];
    int index[thread_num + 1];
    for (int i=0; i<thread_num + 1; ++i)
        index[i] = i * chunk_size;
    for(int i=0; i<thread_num; ++i)
        td[i].join();
    for(int i = 0; i < data_len; ++i){
        int min_index = 0;
        int min_num = numeric_limits<int>::max();
        for(int j=0; j<thread_num; ++j){
            if(index[j]<(j+1)*chunk_size && in_data[index[j]]<min_num){
                min_index = j;
                min_num = in_data[index[j]];
            }
        }
        if(index[thread_num]<data_len&& in_data[index[thread_num]]<min_num){
            min_index = thread_num;
        }
        out_data[i] = in_data[index[min_index]];
        index[min_index]++;
    }
    memcpy(in_data, out_data, sizeof(int)*data_len);
    delete[] out_data;
}
void mt_sort_edge(Edge* in_data, int data_len, int thread_num){
    if(data_len<=1||thread_num==0||data_len<(thread_num+1)*(thread_num+1)){
        sort(in_data, in_data+data_len);
        return;
    }
    int chunk_size = data_len/(thread_num+1);
    if(data_len%(thread_num+1) != 0)
        ++chunk_size;
    thread td[thread_num];
    for(int i=0; i<thread_num; ++i){
        td[i] = thread([=]{
            sort(in_data + i*chunk_size, in_data + (i+1)*chunk_size);
        });
    }
    sort(in_data + chunk_size*thread_num, in_data + data_len);
    Edge* out_data = new Edge[data_len];
    int index[thread_num + 1];
    for(int i=0; i<thread_num+1; i++)
        index[i] = i * chunk_size;
    for(int i=0; i<thread_num; i++)
        td[i].join();
    for(int i = 0; i < data_len; i++){
        int min_index = 0;
        Edge min_num;
        min_num.from = numeric_limits<int>::max();
        for(int j=0; j<thread_num; j++){
            if(index[j]<(j+1)*chunk_size && in_data[index[j]]<min_num){
                min_index = j;
                min_num = in_data[index[j]];
            }
        }
        if(index[thread_num]<data_len&& in_data[index[thread_num]]<min_num){
            min_index = thread_num;
        }
        out_data[i] = in_data[index[min_index]];
        index[min_index]++;
    }
    memcpy(in_data, out_data, sizeof(Edge)*data_len);
    delete[] out_data;
}
struct Node{
    int key,value;
    int nxt;
    inline void set(int k,int v, int n){
        key = k;
        value = v;
        nxt = n;
    }
};
const int hashmap_size = (1<<21);
struct Hashmap{
    Node nodes[MAXE*2];
    int cnt;
    int head[hashmap_size];
    inline void init(){
        cnt = 0;
        memset(head,-1,sizeof(head));
    }
    inline int hash(int x){
        return x>>10;
    }
    inline void set(int key, int value){
        int hs = hash(key);
        nodes[cnt].set(key,value,head[hs]);
        head[hs] = cnt;
        cnt++;
    }
    inline int get(int key){
        int now = head[hash(key)];
        while(now!=-1){
            if(nodes[now].key==key)return nodes[now].value;
            now = nodes[now].nxt;
        }
        return -1;
    }
}*hashmap;
void read(){
    int fd = open(testFile.c_str(), O_RDONLY);
    int test_char_size = (int)lseek(fd, 0, SEEK_END);
    char* test_char = (char*)mmap(NULL, test_char_size, PROT_READ, MAP_PRIVATE, fd, 0);
    char* pt= test_char;
    char* ed = test_char+test_char_size;
    int max_id = -1;
    int e_cnt,from,to;
    ll ccc[3] = {100,10,1};
    ll value;
    e_cnt = from = to = 0;
    value = 0;
    while(pt<ed){
        from = to = 0;
        value = 0;
        while(*pt!=','){
            from = from*10 + *pt - '0';
            pt++;
        }
        pt++;
        while(*pt!=','){
            to = to*10 + *pt - '0';
            pt++;
        }
        pt++;
        while(*pt>='0'){
            value = value*10 + *pt - '0';
            pt++;
        }
        int cc=0;
        if(*pt=='.'){
            pt++;
            while(*pt>='0'){
                value = value*10 + *pt - '0';
                pt++;
                cc++;
            }
        }
        value*=ccc[cc];
        while(*pt!='\n')pt++;
        pt++;
        max_id = max(max(max_id,from),to);
        edges[e_cnt].set(from,to,value);
        e_cnt++;
    }
    e_total = e_cnt;
    v_total = max_id+1;
    mt_sort_edge(edges,e_total,3);
    if(max_id>MAXP){
        mapped = true;
        Edge eg;
        eg.from = MAXP+1;
        eg.to=-1;
        int off = int(lower_bound(edges, edges+e_total, eg)-edges);
        e_cnt = 0;
        for(int i=off;i<e_total;i++){
            index2id[e_cnt++] = edges[i].from;
        }
        int index = 0;
        index2id[index++] = index2id[0];
        for(int i=1;i<e_cnt;i++){
            if(index2id[i-1]==index2id[i])continue;
            index2id[index++] = index2id[i];
        }
        v_total = index + MAXP + 1 ;
        hashmap = new Hashmap();
        hashmap->init();
        for(int i=0;i<index;i++){
            hashmap->set(index2id[i],i + MAXP + 1);
        }
        e_cnt = 0;
        for(int i=0;i<e_total;i++){
            from = edges[i].from;
            to = edges[i].to;
            value = edges[i].value;
            if(from>MAXP){
                from = hashmap->get(from);
            }
            if(to>MAXP){
                to = hashmap->get(to);
                if(to==-1)continue;
            }
            edges[e_cnt++].set(from,to,value);
        }
        e_total = e_cnt;
        delete hashmap;
    }
    for(int i=0;i<e_total;i++){
        redges[i].set(edges[i].to, edges[i].from, edges[i].value);
    }
    mt_sort_edge(redges,e_total,3);
    memset(visit,0,sizeof(bool)*v_total);
    for(int i=0;i<e_total;i++){
        visit[edges[i].from] = 1;
    }
    valid_total = 0;
    for(int i=0;i<v_total;i++){
        if(visit[i]){
            valid_v[valid_total++] = i;
        }
    }
    for(int i=0;i<e_total;i++){
        too[i] = edges[i].to;
        val[i] = edges[i].value;
    }
    for(int i=0;i<e_total;i++){
        rtoo[i] = redges[i].to;
        rval[i] = redges[i].value;
    }
    int pre,nxt;
    for(int i=0;i<=e_total;i++){
        pre = i>0?edges[i-1].from:-1;
        nxt = i<e_total?edges[i].from:v_total;
        for(int j=pre+1;j<=nxt;j++){
            flg[j] = i;
        }
    }
    for(int i=0;i<=e_total;i++){
        pre = i>0?redges[i-1].from:-1;
        nxt = i<e_total?redges[i].from:v_total;
        for(int j=pre+1;j<=nxt;j++){
            rflg[j] = i;
        }
    }
}
void backward(int tid, int s){
    Back* back1 = back[tid];
    int* head1 = head[tid];
    bool* update1 = update[tid];
    int cnt = 0;
    int v1,v2,v3,v4;
    ll a1,a2,a3,a4;
    ll d1,d2,d3,u1,u2,u3;
    for(int i1=rflg[s];i1<rflg[s+1];i1++){
        v1 = rtoo[i1];
        if(v1<=s)continue;
        a1 = rval[i1];
        d1 = a1*5;
        u1 = a1*3;
        for(int i2=rflg[v1];i2<rflg[v1+1];i2++){
            v2 = rtoo[i2];
            if(v2<=s)continue;
            a2 = rval[i2];
            d2 = a2*5;
            u2 = a2*3;
            if(a1>u2||d1<a2)continue;
            for(int i3=rflg[v2];i3<rflg[v2+1];i3++){
                v3 = rtoo[i3];
                if(v3<=s||v3==v1)continue;
                a3 = rval[i3];
                d3 = a3*5;
                u3 = a3*3;
                if(a2>u3||d2<a3)continue;
                for(int i4=rflg[v3];i4<rflg[v3+1];i4++){
                    v4 = rtoo[i4];
                    if(v4<=s||v4==v1||v4==v2)continue;
                    a4 = rval[i4];
                    if(a3>a4*3||d3<a4)continue;
                    back1[cnt].set(v4, v3, v2, v1, a4, a1, head1[v4]);
                    head1[v4] = cnt;
                    cnt++;
                    update1[v4] = true;
                }
            }
        }
    }
    back_cnt[tid][0] = cnt;
}
void do_sort(int tid, int v){
    Back* back1 = back[tid];
    Back* back2 = back_sort[tid];
    int st = back_sort_cnt[tid][0];
    int ed = st;
    int now = head[tid][v];
    int cnt = 0;
    while(now!=-1){
        cnt++;
        back2[ed++] = back1[now];
        now = back1[now].nxt;
    }
    back_sort_cnt[tid][0] = ed;
    back_idx[tid][v*2] = st;
    back_idx[tid][v*2+1] = ed;
    sorted[tid][v] = true;
    if(ed-st>1)
        sort(back2+st,back2+ed);
}
void foreward(int tid, int s){
    Back* back1 = back_sort[tid];
    int* back_idx1 = back_idx[tid];
    bool* update1 = update[tid];
    bool* sorted1 = sorted[tid];
    int cnt[6];
    for(int i=0;i<6;i++){
        cnt[i] = ans_cnt[tid][i];
    }
    int v1,v2,v3,v4,v5,v6,v7;
    ll a1,a2,a3,a4,a5,a6,a7,a8;
    ll d1,d2,d3,d4;
    ll u1,u2,u3,u4;
    for(int i1=flg[s];i1<flg[s+1];i1++){
        v1 = too[i1];
        if(v1<=s)continue;
        a1 = val[i1];
        d1 = a1*5;
        u1 = a1*3;
        if(update1[v1]){
            if(!sorted1[v1]){
                do_sort(tid,v1);
            }
            for(int k1=back_idx1[v1*2];k1<back_idx1[v1*2+1];k1++){
                a2 = back1[k1].a;
                a5 = back1[k1].b;
                if(a1>a2*5||a2>u1||a5>d1||a1>a5*3)continue;
                v2 = back1[k1].s[1];
                v3 = back1[k1].s[2];
                v4 = back1[k1].s[3];
                Ans& a = ans[tid][2][cnt[2]++];
                a.len = 5;
                a.num[0] = s;
                a.num[1] = v1;
                a.num[2] = v2;
                a.num[3] = v3;
                a.num[4] = v4;
            }
        }
        for(int i2=flg[v1];i2<flg[v1+1];i2++){
            v2 = too[i2];
            if(v2<=s)continue;
            a2 = val[i2];
            d2 = a2*5;
            u2 = a2*3;
            if(a2>u1||d2<a1)continue;
            if(update1[v2]){
                if(!sorted1[v2]){
                    do_sort(tid,v2);
                }
                for(int k2=back_idx1[v2*2];k2<back_idx1[v2*2+1];k2++){
                    a3 = back1[k2].a;
                    a6 = back1[k2].b;
                    if(a2>a3*5||a3>u2||a6>d1||a1>a6*3)continue;
                    v3 = back1[k2].s[1];
                    v4 = back1[k2].s[2];
                    v5 = back1[k2].s[3];
                    if (v3 == v1 || v4 == v1 || v5 == v1)continue;
                    Ans& a = ans[tid][3][cnt[3]++];
                    a.len = 6;
                    a.num[0] = s;
                    a.num[1] = v1;
                    a.num[2] = v2;
                    a.num[3] = v3;
                    a.num[4] = v4;
                    a.num[5] = v5;
                }
            }
            for(int i3=flg[v2];i3<flg[v2+1];i3++){
                v3 = too[i3];
                if(v3<s)continue;
                if(v3==s){
                    a3 = val[i3];
                    d3 = a3*5;
                    u3 = a3*3;
                    if(a3>u2||d3<a2||a3>d1||a1>u3)continue;
                    Ans& a = ans[tid][0][cnt[0]++];
                    a.len = 3;
                    a.num[0] = s;
                    a.num[1] = v1;
                    a.num[2] = v2;
                    continue;
                }
                a3 = val[i3];
                d3 = a3*5;
                u3 = a3*3;
                if(a3>u2||d3<a2)continue;
                if(v3 == v1)continue;
                if(update1[v3]){
                    if(!sorted1[v3]){
                        do_sort(tid,v3);
                    }
                    for(int k3=back_idx1[v3*2];k3<back_idx1[v3*2+1];k3++){
                        a4 = back1[k3].a;
                        a7 = back1[k3].b;
                        if(a3>a4*5||a4>u3||a7>d1||a1>a7*3)continue;
                        v4 = back1[k3].s[1];
                        v5 = back1[k3].s[2];
                        v6 = back1[k3].s[3];
                        if (v4 == v1 || v4 == v2 || v5 == v1 || v5 == v2 || v6 == v1 || v6 == v2)continue;
                        Ans& a = ans[tid][4][cnt[4]++];
                        a.len = 7;
                        a.num[0] = s;
                        a.num[1] = v1;
                        a.num[2] = v2;
                        a.num[3] = v3;
                        a.num[4] = v4;
                        a.num[5] = v5;
                        a.num[6] = v6;
                    }
                }
                for(int i4=flg[v3];i4<flg[v3+1];i4++){
                    v4 = too[i4];
                    if(v4==s){
                        a4 = val[i4];
                        d4 = a4*5;
                        u4 = a4*3;
                        if(a4>u3||d4<a3||a4>d1||a1>u4)continue;
                        Ans& a = ans[tid][1][cnt[1]++];
                        a.len = 4;
                        a.num[0] = s;
                        a.num[1] = v1;
                        a.num[2] = v2;
                        a.num[3] = v3;
                        continue;
                    }
                    if(update1[v4]){
                        a4 = val[i4];
                        u4 = a4*3;
                        if(a4>u3||a4*5<a3)continue;
                        if(v4 == v1 || v4 == v2)continue;
                        if(!sorted1[v4]){
                            do_sort(tid,v4);
                        }
                        for(int k4=back_idx1[v4*2];k4<back_idx1[v4*2+1];k4++){
                            a5 = back1[k4].a;
                            a8 = back1[k4].b;
                            if(a4>a5*5||a5>u4||a8>d1||a1>a8*3)continue;
                            v5 = back1[k4].s[1];
                            v6 = back1[k4].s[2];
                            v7 = back1[k4].s[3];
                            if (v5 == v1 || v5 == v2 || v5 == v3)continue;
                            if (v6 == v1 || v6 == v2 || v6 == v3)continue;
                            if (v7 == v1 || v7 == v2 || v7 == v3)continue;
                            Ans& a = ans[tid][5][cnt[5]++];
                            a.len = 8;
                            a.num[0] = s;
                            a.num[1] = v1;
                            a.num[2] = v2;
                            a.num[3] = v3;
                            a.num[4] = v4;
                            a.num[5] = v5;
                            a.num[6] = v6;
                            a.num[7] = v7;
                        }
                    }
                }
            }
        }
    }
    back_sort_cnt[tid][0] = 0;
    for(int i=0;i<back_cnt[tid][0];i++){
        int k = back[tid][i].s[0];
        sorted1[k] = false;
        update1[k] = false;
        head[tid][k] = -1;
    }
    ans_v_cnt[s*32] = tid;
    for(int i=0;i<6;i++){
        ans_v_cnt[s*32+i+1] = cnt[i] - ans_cnt[tid][i];
        ans_cnt[tid][i] = cnt[i];
    }
}
void search_mt(int tid){
    for(int i=0;i<6;i++){
        ans[tid][i] = new Ans[MAXA];
    }
    memset(head[tid],-1,sizeof(int)*v_total);
    memset(update[tid],0,sizeof(bool)*v_total);
    back[tid] = new Back[MAXA];
    back_sort[tid] = new Back[MAXA];
    
    int i;
    while(true){
        i = mtx_num++;
        if(i>=valid_total)break;
        int j = valid_v[i];
        backward(tid,j);
        foreward(tid,j);
    }
    delete []back[tid];
    delete []back_sort[tid];
    
}
void search(){
    memset(back_sort_cnt,0,sizeof(back_sort_cnt));
    memset(ans_cnt,0,sizeof(ans_cnt));
    memset(ans_v_cnt,0,sizeof(int)*v_total*32);
    thread td[3];
    for(int i=0;i<3;i++){
        td[i] = thread(search_mt,i+1);
    }
    search_mt(0);
    for(int i=0;i<3;i++) td[i].join();
    ans_total = 0;
    for(int i=0;i<4;i++)
        for(int j=0;j<6;j++){
            ans_total += ans_cnt[i][j];
        }
}
void merge(){
    ans_sorted = new Ans*[ans_total];
    int ans_now[4][6];
    memset(ans_now,0,sizeof(ans_now));
    int cnt=0;
    for(int k=0;k<6;k++){
        for(int i=0;i<valid_total;i++){
            int j = valid_v[i];
            int tid = ans_v_cnt[j*32];
            for(int r=0;r<ans_v_cnt[j*32+1+k];r++){
                ans_sorted[cnt++] = &ans[tid][k][ans_now[tid][k]++];
            }
        }
    }
}
void trans_mt(int tid, int st, int ed){
    if(mapped){
        Ans* pt;
        for(int i=st;i<ed;i++){
            pt = ans_sorted[i];
            int len = pt->len;
            for(int j=0;j<len;j++){
                if(pt->num[j]>MAXP)
                    pt->num[j] = index2id[pt->num[j]-MAXP-1];
            }
        }
    }
    ans_out[tid] = new char[88*(ed-st)+10];
    char* p = ans_out[tid];
    if(tid==0){
        p += snprintf(p, 20 , "%d\n", ans_total);
    }
    Ans* pt;
    for(int i=st;i<ed;i++){
        pt = ans_sorted[i];
        p += u32toa_jeaiii(pt->num[0], p);
        int len = pt->len;
        for(int j=1;j<len;j++){
            *(p++) = ',';
            p += u32toa_jeaiii(pt->num[j], p);
        }
        *(p++) = '\n';
    }
    ans_out_len[tid][0] = int(p-ans_out[tid]);
    *(p++) = '\0';
}
void trans(){
    int st[4],ed[4];
    int cnt[6];
    int avg = 0;
    for(int i=0;i<6;i++){
        cnt[i] = 0;
        for(int j=0;j<4;j++)
            cnt[i]+=ans_cnt[j][i];
        avg+=(i+1)*cnt[i];
    }
    avg/=4;
    int now = 0;
    for(int i=0;i<4;i++){
        st[i] = now;
        int ext = avg;
        for(int j=0;j<6;j++){
            if(cnt[j]==0)continue;
            if(cnt[j]*(j+1)<=ext){
                ext -= cnt[j]*(j+1);
                now += cnt[j];
                cnt[j]=0;
            }
            else{
                now += ext/(j+1);
                cnt[j] -= ext/(j+1);
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
    for(int i=0;i<4;i++)
        for(int j=0;j<6;j++)
            delete []ans[i][j];
    delete []ans_sorted;
}
void save_mt(int tid, char* out){
    int offset = 0;
    for(int i=0;i<tid;i++) offset += ans_out_len[i][0];
    memcpy(out+offset, ans_out[tid], ans_out_len[tid][0]);
}
void save(){
    /*timeval t_start, t_end;
     gettimeofday( &t_start, NULL);
     gettimeofday( &t_end, NULL);
     double delta_t = (t_end.tv_sec-t_start.tv_sec) + (t_end.tv_usec-t_start.tv_usec)/1000000.0;
     cout<<"save:"<<delta_t<<"s"<<endl;*/
    int length = 0;
    for(int i=0;i<4;i++){
        length += ans_out_len[i][0];
    }
    int fd = open(resultFile.c_str(), O_RDWR | O_CREAT, 0666);
    char* out = (char*)mmap(NULL,length,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);
    lseek(fd, length-1, SEEK_SET);
    write(fd, "\0", 1);
    thread td[3];
    for(int i=0;i<3;i++){
        td[i] = thread(save_mt,i,out);
    }
    save_mt(3,out);
    for(int i=0;i<3;i++)td[i].join();
    munmap(out, length);
    close(fd);
    for(int i=0;i<4;i++)
        delete []ans_out[i];
}
int main(){
    read();
    search();
    //cout<<ans_total<<endl;
    merge();
    trans();
    save();
    return 0;
}
