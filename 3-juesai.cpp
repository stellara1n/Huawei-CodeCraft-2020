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
#include <queue>
#include <cstdio>
#include <unordered_map>
using namespace std;
string testFile = "/data/test_data.txt";
string resultFile = "/projects/student/result.txt";
#define MAXE 2500005
#define MAXV 1000005
#define INF  4294967295
#define uint16_INF 65535
#define STEP 15
int e_total,v_total;
atomic<int> mtx_num(0);
bool flag = false;
struct Edge1{
    int from,to,cost;
    inline void set(int f, int t, int c){
        from = f;
        to = t;
        cost = c;
    }
}full_edges[MAXE];
int max_cost = 0;
int cmp_x(const Edge1& a, const Edge1& b){
    if(a.from == b.from){
        if(a.cost == b.cost) return a.to<b.to;
        else return a.cost < b.cost;
    }
    else return a.from<b.from;
}
int cmp_y(const Edge1& a, const Edge1& b){
    return a.to<b.to;
}
struct Edge2{
    int to;
    int cost;
    inline void set(int t, int c){
        to = t;
        cost = c;
    }
}edges[MAXE];
bool visit[MAXV];
int index2id[MAXV];
int newindex2id[MAXV];
int newid2index[MAXV];
int suffix[MAXV];
int degree_in[MAXV];
int degree_out[MAXV];
uint16_t zero[MAXV];
struct Ans{
    int id;double value;
    bool operator < (const Ans & b) const{
        if(abs(value - b.value)<=0.0001)return id<b.id;
        else return value > b.value;
    }
}ans[MAXV];
#define MAXP 5000
#define MAXC 10000
struct Node{
    uint32_t dis;
    int id;
    inline void set(uint32_t d, int x){
        dis = d;
        id = x;
    }
};
struct Heap{
    Node val[MAXV];
    int inq[MAXV];
    int qsize;
    void init(){
        qsize = 0;
    }
    inline void down(int x){
        uint32_t tmp = val[x].dis;
        int tmp_id = val[x].id;
        int now = x;
        int son = (now-1)*8+2;
        while(son<=qsize){
            uint32_t tmp_2 = val[son].dis;
            int ed = min(qsize,son+7);
            for(int i=son+1;i<=ed;i++){
                if(val[i].dis < tmp_2){
                    tmp_2 = val[i].dis;
                    son = i;
                }
            }
            if(tmp_2<tmp){
                val[now] = val[son];
                inq[val[now].id] = now;
                now = son;
                son = (now-1)*8+2;
            }
            else break;
        }
        val[now].dis = tmp;
        val[now].id = tmp_id;
        inq[tmp_id] = now;
    }
    inline void up(int x){
        uint32_t tmp = val[x].dis;
        int tmp_id = val[x].id;
        int now = x;
        int par = (now-2)/8+1;
        while(par<now){
            if(tmp<val[par].dis){
                val[now] = val[par];
                inq[val[now].id] = now;
                now = par;
                par = (now-2)/8+1;
            }
            else break;
        }
        val[now].dis = tmp;
        val[now].id = tmp_id;
        inq[tmp_id] = now;
    }
    int pop(){
        int r = val[1].id;
        inq[r] = 0;
        if(qsize>1){
            val[1] = val[qsize];
            qsize--;
            down(1);
            return r;
        }
        else{
            qsize--;
            return r;
        }
    }
    void push(uint32_t d, int x){
        int pos = inq[x];
        if(pos==0){
            ++qsize;
            val[qsize].dis = d;
            val[qsize].id = x;
            up(qsize);
        }
        else{
            val[pos].dis = d;
            up(pos);
        }
    }
    bool empty(){
        return qsize == 0;
    }
};
struct Q{
    int l,r;
    int a[MAXC];
    Q(){
        l = r = 0;
    }
    void push(int x){
        a[r] = x;
        r = (r+1)%MAXC;
    }
    int front(){
        return a[l];
    }
    void pop(){
        l = (l+1)%MAXC;
    }
    bool empty(){
        return l == r;
    }
};
struct PQ{
    Q q[MAXP];
    Heap qq;
    int head;
    void init(){
        head = MAXP;
    }
    void push(uint32_t x, int v){
        if(x<MAXP){
            q[x].push(v);
            if(head>x) head = (int)x;
        }
        else qq.push(x, v);
    }
    void top(uint32_t& d, int& x){
        if(head<MAXP){
            d = head;
            x = q[head].front();
        }
        else{
            d = qq.val[1].dis;
            x = qq.val[1].id;
        }
    }
    int pop(){
        if(head<MAXP){
            int r = q[head].front();
            q[head].pop();
            while(q[head].empty()&&head<MAXP)head++;
            return r;
        }
        else return qq.pop();
    }
    bool empty(){
        return head == MAXP && qq.empty();
    }
};
struct Node2{
    uint16_t dis;
    int id;
    inline void set(uint16_t d, int x){
        dis = d;
        id = x;
    }
};
struct Heap2{
    Node2 val[MAXV];
    int inq[MAXV];
    int qsize;
    void init(){
        qsize = 0;
    }
    inline void down(int x){
        uint16_t tmp = val[x].dis;
        int tmp_id = val[x].id;
        int now = x;
        int son = (now-1)*8+2;
        while(son<=qsize){
            uint16_t tmp_2 = val[son].dis;
            int ed = min(qsize,son+7);
            for(int i=son+1;i<=ed;i++){
                if(val[i].dis < tmp_2){
                    tmp_2 = val[i].dis;
                    son = i;
                }
            }
            if(tmp_2<tmp){
                val[now] = val[son];
                inq[val[now].id] = now;
                now = son;
                son = (now-1)*8+2;
            }
            else break;
        }
        val[now].dis = tmp;
        val[now].id = tmp_id;
        inq[tmp_id] = now;
    }
    inline void up(int x){
        uint16_t tmp = val[x].dis;
        int tmp_id = val[x].id;
        int now = x;
        int par = (now-2)/8+1;
        while(par<now){
            if(tmp<val[par].dis){
                val[now] = val[par];
                inq[val[now].id] = now;
                now = par;
                par = (now-2)/8+1;
            }
            else break;
        }
        val[now].dis = tmp;
        val[now].id = tmp_id;
        inq[tmp_id] = now;
    }
    int pop(){
        int r = val[1].id;
        inq[r] = 0;
        if(qsize>1){
            val[1] = val[qsize];
            qsize--;
            down(1);
            return r;
        }
        else{
            qsize--;
            return r;
        }
    }
    void push(uint16_t d, int x){
        int pos = inq[x];
        if(pos==0){
            ++qsize;
            val[qsize].dis = d;
            val[qsize].id = x;
            up(qsize);
        }
        else{
            val[pos].dis = d;
            up(pos);
        }
    }
    bool empty(){
        return qsize == 0;
    }
};
struct Q2{
    int l,r;
    int a[MAXC];
    Q2(){
        l = r = 0;
    }
    void push(int x){
        a[r] = x;
        r = (r+1)%MAXC;
    }
    int front(){
        return a[l];
    }
    void pop(){
        l = (l+1)%MAXC;
    }
    bool empty(){
        return l == r;
    }
};
struct PQ2{
    Q2 q[MAXP];
    Heap2 qq;
    uint16_t head;
    void init(){
        head = MAXP;
    }
    void push(uint16_t x, int v){
        if(x<MAXP){
            q[x].push(v);
            if(head>x) head = (int)x;
        }
        else qq.push(x, v);
    }
    void top(uint16_t& d, int& x){
        if(head<MAXP){
            d = head;
            x = q[head].front();
        }
        else{
            d = qq.val[1].dis;
            x = qq.val[1].id;
        }
    }
    int pop(){
        if(head<MAXP){
            int r = q[head].front();
            q[head].pop();
            while(q[head].empty()&&head<MAXP)head++;
            return r;
        }
        else return qq.pop();
    }
    bool empty(){
        return head == MAXP && qq.empty();
    }
};
void read(){
    int fd = open(testFile.c_str(), O_RDONLY);
    int test_char_size = (int)lseek(fd, 0, SEEK_END);
    char* test_char = (char*)mmap(NULL, test_char_size, PROT_READ, MAP_PRIVATE, fd, 0);
    char* pt= test_char;
    char* ed = test_char+test_char_size;
    int e_cnt,from,to,cost;
    e_cnt = from = to = cost = 0;
    max_cost = 0;
    while(pt<ed){
        from = to = cost = 0;
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
            cost = cost*10 + *pt - '0';
            pt++;
        }
        while(*pt!='\n')pt++;
        pt++;
        if(cost==0)continue;
        max_cost = max(max_cost,cost);
        index2id[e_cnt*2] = from;
        index2id[e_cnt*2+1] = to;
        full_edges[e_cnt++].set(from, to, cost);
    }
    //cout<<max_cost<<endl;
    //id table
    sort(index2id,index2id+e_cnt*2);
    int v_cnt = 0;
    index2id[v_cnt++] = index2id[0];
    for(int i=1;i<e_cnt*2;i++){
        if(index2id[i-1]==index2id[i])continue;
        index2id[v_cnt++] = index2id[i];
    }
    e_total = e_cnt;
    v_total = v_cnt;
    //cout<<e_total<<' '<<v_total<<endl;
    //cout<<e_total*1.0/v_total<<endl;
    //map
    sort(full_edges,full_edges+e_total,cmp_y);
    v_cnt = 0;
    for(int i=0;i<e_total;i++){
        int y = full_edges[i].to;
        while(index2id[v_cnt] < y)
            v_cnt++;
        full_edges[i].to = v_cnt;
    }
    sort(full_edges,full_edges+e_total,cmp_x);
    v_cnt = 0;
    for(int i=0;i<e_total;i++){
        int x = full_edges[i].from;
        while(index2id[v_cnt] < x)
            v_cnt++;
        full_edges[i].from = v_cnt;
    }
    //suffix
    int pre,nxt;
    for(int i=0;i<=e_total;i++){
        pre = i>0?full_edges[i-1].from:-1;
        nxt = i<e_total?full_edges[i].from:v_total;
        for(int j=pre+1;j<=nxt;j++){
            suffix[j] = i;
        }
    }
    
    //reindex
    int newid = 0;
    memset(visit,0,sizeof(bool)*v_total);
    queue<int> q;
    for(int i=0;i<v_total;i++){
        if(!visit[i]){
            q.push(i);
            while(!q.empty()){
                int u = q.front();
                q.pop();
                if(visit[u])continue;
                visit[u] = true;
                newindex2id[newid] = index2id[u];
                newid2index[u] = newid;
                newid++;
                for(int j=suffix[u];j<suffix[u+1];j++){
                    int v = full_edges[j].to;
                    if(!visit[v])q.push(v);
                }
            }
        }
    }
    
    for(int i=0;i<e_total;i++){
        full_edges[i].from = newid2index[full_edges[i].from];
        full_edges[i].to = newid2index[full_edges[i].to];
    }
    sort(full_edges,full_edges+e_total,cmp_x);
    
    //suffix
    for(int i=0;i<=e_total;i++){
        pre = i>0?full_edges[i-1].from:-1;
        nxt = i<e_total?full_edges[i].from:v_total;
        for(int j=pre+1;j<=nxt;j++){
            suffix[j] = i;
        }
    }

    //small edge
    for(int i=0;i<e_total;i++){
        edges[i].set(full_edges[i].to, full_edges[i].cost);
    }
    //degree
    memset(degree_in,0,sizeof(int)*v_total);
    memset(degree_out,0,sizeof(int)*v_total);
    memset(zero,0,sizeof(uint16_t)*v_total);
    for(int i=0;i<e_total;i++){
        degree_out[full_edges[i].from]++;
        degree_in[full_edges[i].to]++;
    }
    for(int i=0;i<v_total;i++){
        if(degree_in[i]==0&&degree_out[i]==1){
            zero[edges[suffix[i]].to]++;
        }
    }
    
}
struct Prev{
    int x[MAXV][1];
    int y[MAXV][100];
    int len[MAXV];
    void push_back(const int& v, const int& u){
        if(len[v]==1)y[v][0]= x[v][0];
        y[v][len[v]++] = u;
    }
    void push_one(const int& v, const int& u){
        len[v] = 1;
        x[v][0] = u;
    }
    int size(const int& v){
        return len[v];
    }
    void clear(const int& v){
        len[v] = 0;
    }
    void clear_all(){
        memset(len,0,sizeof(int)*v_total);
    }
    int* operator [](const int& v){
        return len[v]>1?y[v]:x[v];
    }
};

struct Data{
    PQ* que;
    uint32_t dis[MAXV];
    int16_t num[MAXV];
    int top[MAXV];
    Prev* pre;
    double dps[MAXV];
    double centrality[MAXV];
}data_array1[16];
void search1(int tid, int s){
    Data* data = data_array1 + tid;
    PQ* q = data->que;
    Prev* pre = data->pre;
    uint32_t* dis = data->dis;
    int16_t* num = data->num;
    int* top = data->top;
    double* dps = data->dps;
    double* centrality = data->centrality;

    int top_cnt = 0;
    dis[s] = 0;
    num[s] = 1;
    q->push(0,s);
    int u,v;uint32_t dis_u;
    while(!q->empty()){
        q->top(dis_u, u);
        q->pop();
        if(dis_u!=dis[u])continue;
        top[top_cnt++] = u;
        for(int i=suffix[u];i<suffix[u+1];i++){
            v = edges[i].to;
            uint32_t cc = dis_u + edges[i].cost;
            if(dis[v] > cc){
                dis[v] = cc;
                num[v] = num[u];
                pre->push_one(v, u);
                q->push(cc, v);
            }
            else if(dis[v] == cc){
                num[v] += num[u];
                pre->push_back(v, u);
            }
        }
    }
    uint16_t z = zero[s]+1;
    for(int i=top_cnt-1;i>0;i--){
        int w = top[i];
        double dps_div_num_w = (dps[w]+1)/num[w];
        for(int j=0;j<pre->size(w);j++){
            int v = (*pre)[w][j];
            dps[v] += num[v]*dps_div_num_w;
        }
        centrality[w] += dps[w]*z;
    }
    centrality[s] += dps[s]*(z-1);
    for(int i=0;i<top_cnt;i++){
        int u = top[i];
        dps[u] = 0;
        dis[u] = INF;
    }
}
void solve_mt1(int tid){
    Data* data = data_array1 + tid;
    memset(data->dis,0xffff,sizeof(uint32_t)*v_total);
    memset(data->num,0,sizeof(int16_t)*v_total);
    memset(data->dps,0,sizeof(double)*v_total);
    memset(data->centrality,0,sizeof(double)*v_total);
    data->que = new PQ;
    data->que->init();
    data->pre = new Prev;
    data->pre->clear_all();
    int s,st,ed;
    while(true){
        s = mtx_num++;
        st = s*STEP;
        if(st>=v_total)break;
        ed = min(v_total,(s+1)*STEP);
        for(int i=st;i<ed;i++){
            if(degree_out[i]==0 || (degree_in[i]==0&&degree_out[i]==1))continue;
            search1(tid,i);
        }
    }
}
void solve1(){
    thread td[15];
    for(int i=0;i<15;i++){
        td[i] = thread(solve_mt1,i);
    }
    solve_mt1(15);
    for(int i=0;i<15;i++)
        td[i].join();
    for(int i=0;i<v_total;i++){
        ans[i].id = newindex2id[i];
        ans[i].value = 0;
    }
    for(int k=0;k<16;k++){
        for(int i=0;i<v_total;i++){
            ans[i].value += data_array1[k].centrality[i];
        }
    }
    sort(ans,ans+v_total);
}
struct Edge3{
    int to;
    uint16_t cost;
    inline void set(int t, uint16_t c){
        to = t;
        cost = c;
    }
}edges2[MAXE];

struct Data2{
    PQ2* que;
    uint16_t dis[MAXV];
    int16_t num[MAXV];
    int top[MAXV];
    Prev* pre;
    double dps[MAXV];
    double centrality[MAXV];
}data_array2[16];
void search2(int tid, int s){
    Data2* data = data_array2+tid;
    PQ2* q = data->que;
    Prev* pre = data->pre;
    uint16_t* dis = data->dis;
    int16_t* num = data->num;
    int* top = data->top;
    double* dps = data->dps;
    double* centrality = data->centrality;

    int top_cnt = 0;
    dis[s] = 0;
    num[s] = 1;
    q->push(0,s);
    int u,v;uint16_t dis_u;
    while(!q->empty()){
        q->top(dis_u, u);
        q->pop();
        if(dis_u!=dis[u])continue;
        top[top_cnt++] = u;
        for(int i=suffix[u];i<suffix[u+1];i++){
            v = edges2[i].to;
            uint16_t cc = dis_u + edges2[i].cost;
            if(dis[v] > cc){
                dis[v] = cc;
                num[v] = num[u];
                pre->push_one(v, u);
                q->push(cc, v);
            }
            else if(dis[v] == cc){
                num[v] += num[u];
                pre->push_back(v, u);
            }
        }
    }
    uint16_t z = zero[s]+1;
    for(int i=top_cnt-1;i>0;i--){
        int w = top[i];
        double dps_div_num_w = (dps[w]+1)/num[w];
        for(int j=0;j<pre->size(w);j++){
            int v = (*pre)[w][j];
            dps[v] += num[v]*dps_div_num_w;
        }
        centrality[w] += dps[w]*z;
    }
    centrality[s] += dps[s]*(z-1);
    for(int i=0;i<top_cnt;i++){
        int u = top[i];
        dps[u] = 0;
        dis[u] = uint16_INF;
    }
}
void solve_mt2(int tid){
    Data2* data = data_array2 + tid;
    memset(data->dis,0xffff,sizeof(uint16_t)*v_total);
    memset(data->num,0,sizeof(int16_t)*v_total);
    memset(data->dps,0,sizeof(double)*v_total);
    memset(data->centrality,0,sizeof(double)*v_total);
    data->que = new PQ2;
    data->que->init();
    data->pre = new Prev;
    data->pre->clear_all();
    int s,st,ed;
    while(true){
        s = mtx_num++;
        st = s*STEP;
        if(st>=v_total)break;
        ed = min(v_total,(s+1)*STEP);
        for(int i=st;i<ed;i++){
            if(degree_out[i]==0 || (degree_in[i]==0&&degree_out[i]==1))continue;
            search2(tid,i);
        }
    }
}
void solve2(){
    for(int i=0;i<e_total;i++){
        edges2[i].set(edges[i].to, edges[i].cost);
    }
    thread td[15];
    for(int i=0;i<15;i++){
        td[i] = thread(solve_mt2,i);
    }
    solve_mt2(15);
    for(int i=0;i<15;i++)
        td[i].join();
    for(int i=0;i<v_total;i++){
        ans[i].id = newindex2id[i];
        ans[i].value = 0;
    }
    for(int k=0;k<16;k++){
        for(int i=0;i<v_total;i++){
            ans[i].value += data_array2[k].centrality[i];
        }
    }
    sort(ans,ans+v_total);
}
void save(){
    char* ans_out = new char[20000];
    char* p = ans_out;
    for(int i=0;i<min(v_total,100);i++){
        p += snprintf(p, 200 , "%d,%.3lf\n", ans[i].id, ans[i].value);
    }
    size_t len = p - ans_out;
    int fd = open(resultFile.c_str(), O_RDWR | O_CREAT, 0666);
    write(fd, ans_out, len);
    close(fd);
    delete [] ans_out;
}
int main() {
    
    read();
    if(e_total<500000 || max_cost>127){
        solve1();
    }
    else {
        solve2();
    }
    save();
    /*
    for(int i=0;i<10;i++){
        printf("%d,%.3lf\n",ans[i].id,ans[i].value);
    }*/
    return 0;
}
