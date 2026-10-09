// =====================================================================
//  Independent enumeration & verification of hyperstructures of order n
//  (n = 3, 4).  Emits the complete machine-readable classification.
//  Written directly from the axioms; no code reused from elsewhere.
// =====================================================================
#include <bits/stdc++.h>
using namespace std;

int N;                       // order
typedef unsigned char Sub;   // bitmask over N <= 4 elements
int NPERM; vector<array<int,4>> PERM;

static void initPerms(){
    vector<int> p; for(int i=1;i<N;i++) p.push_back(i);
    sort(p.begin(),p.end()); PERM.clear();
    do{ array<int,4> q{}; q[0]=0; for(int i=0;i<(int)p.size();i++) q[i+1]=p[i]; PERM.push_back(q);}while(next_permutation(p.begin(),p.end()));
    NPERM=PERM.size();
}
static inline Sub permSub(Sub s,const array<int,4>&p){ Sub r=0; for(int i=0;i<N;i++) if(s>>i&1) r|=(Sub)(1<<p[i]); return r; }

// ---------- encodings ----------
static string hexchar(int v){ const char*h="0123456789abcdef"; return string(1,h[v]); }
static string codePGraw(const Sub t[4][4]){ string s; for(int i=1;i<N;i++)for(int j=1;j<N;j++) s+=hexchar(t[i][j]); return s; }
static string codeSGraw(const int m[4][4]){ string s; for(int i=0;i<N;i++)for(int j=1;j<N;j++) s+=hexchar(m[i][j]); return s; }
static string codePG(const Sub t[4][4]);
static string codeSG(const int m[4][4]);
static uint64_t keyPG(const Sub t[4][4]){ uint64_t k=0; for(int i=1;i<N;i++)for(int j=1;j<N;j++) k=(k<<4)|t[i][j]; return k; }
static uint64_t keySG(const int m[4][4]){ uint64_t k=0; for(int i=0;i<N;i++)for(int j=1;j<N;j++) k=(k<<2)|(uint64_t)m[i][j]; return k; }
static void applyPG(const Sub t[4][4], const array<int,4>&p, Sub out[4][4]){
    for(int i=0;i<N;i++)for(int j=0;j<N;j++) out[p[i]][p[j]]=permSub(t[i][j],p); }
static void applySG(const int m[4][4], const array<int,4>&p, int out[4][4]){
    for(int i=0;i<N;i++)for(int j=0;j<N;j++) out[p[i]][p[j]]=p[m[i][j]]; }
static string codePG(const Sub t[4][4]){ string b; for(auto&p:PERM){ Sub o[4][4]; applyPG(t,p,o); string c=codePGraw(o); if(b.empty()||c<b)b=c; } return b; }
static string codeSG(const int m[4][4]){ string b; for(auto&p:PERM){ int o[4][4]; applySG(m,p,o); string c=codeSGraw(o); if(b.empty()||c<b)b=c; } return b; }

// ---------- axioms ----------
static bool assocHyper(const Sub t[4][4]){
    for(int i=0;i<N;i++)for(int j=0;j<N;j++)for(int k=0;k<N;k++){
        Sub l=0,r=0;
        for(int s=0;s<N;s++) if(t[i][j]>>s&1) l|=t[s][k];
        for(int s=0;s<N;s++) if(t[j][k]>>s&1) r|=t[i][s];
        if(l!=r) return false; }
    return true; }
static bool reversible(const Sub t[4][4], const int inv[4]){
    for(int x=0;x<N;x++)for(int y=0;y<N;y++)for(int z=0;z<N;z++) if(t[y][z]>>x&1){
        if(!((t[x][inv[z]]>>y)&1)) return false;
        if(!((t[inv[y]][x]>>z)&1)) return false; }
    return true; }
static bool partialOK(const Sub t[4][4]){
    for(int i=0;i<N;i++)for(int j=0;j<N;j++)for(int k=0;k<N;k++){
        if(!t[i][j]||!t[j][k]) continue;
        bool rdy=true;
        for(int s=0;s<N;s++) if((t[i][j]>>s&1) && !t[s][k]) rdy=false;
        for(int s=0;s<N;s++) if((t[j][k]>>s&1) && !t[i][s]) rdy=false;
        if(!rdy) continue;
        Sub l=0,r=0;
        for(int s=0;s<N;s++) if(t[i][j]>>s&1) l|=t[s][k];
        for(int s=0;s<N;s++) if(t[j][k]>>s&1) r|=t[i][s];
        if(l!=r) return false; }
    return true; }

// ---------- fundamental relation ----------
struct UF{ int p[4]; UF(){for(int i=0;i<4;i++)p[i]=i;} int f(int x){return p[x]==x?x:p[x]=f(p[x]);} void u(int a,int b){a=f(a);b=f(b);if(a!=b)p[a]=b;} };
static void betaStar(const vector<array<array<Sub,4>,4>>& ops, int cls[4]){
    set<Sub> F; for(int i=0;i<N;i++) F.insert((Sub)(1<<i));
    bool ch=true;
    while(ch){ ch=false; vector<Sub> cur(F.begin(),F.end());
        for(Sub A:cur) for(Sub B:cur) for(auto&op:ops){
            Sub r=0; for(int a=0;a<N;a++) if(A>>a&1) for(int b=0;b<N;b++) if(B>>b&1) r|=op[a][b];
            if(r && !F.count(r)){ F.insert(r); ch=true; } } }
    UF uf; for(Sub U:F){ int f=-1; for(int i=0;i<N;i++) if(U>>i&1){ if(f<0)f=i; else uf.u(f,i);} }
    for(int i=0;i<N;i++) cls[i]=uf.f(i); }
static string quotientGroup(const Sub t[4][4], const int cls[4]){
    map<int,int> idx; for(int i=0;i<N;i++) if(!idx.count(cls[i])){ int n=idx.size(); idx[cls[i]]=n; }
    int n=idx.size(); vector<vector<int>> g(n, vector<int>(n,-1));
    for(int i=0;i<N;i++)for(int j=0;j<N;j++){
        int target=-1;
        for(int s=0;s<N;s++) if(t[i][j]>>s&1){ int c=idx.at(cls[s]); if(target<0)target=c; else if(target!=c) return "NOTWELLDEF"; }
        int A=idx.at(cls[i]),B=idx.at(cls[j]);
        if(g[A][B]<0) g[A][B]=target; else if(g[A][B]!=target) return "NOTWELLDEF"; }
    if(n==1) return "1"; if(n==2) return "Z2"; if(n==3) return "Z3";
    if(n==4){ int id=-1; for(int i=0;i<n;i++){ bool ok=true; for(int j=0;j<n;j++) if(g[i][j]!=j||g[j][i]!=j) ok=false; if(ok)id=i; }
        if(id<0) return "NOTGROUP";
        for(int i=0;i<n;i++) if(g[i][i]!=id) return "Z4";
        return "Z2xZ2"; }
    return "?"; }
static string autName(int a){ return a==1?"1":a==2?"Z2":a==3?"Z3":a==6?"S3":"?"; }

// ---------- globals ----------
vector<array<array<Sub,4>,4>> allPG; vector<array<int,4>> allPGinv;
vector<array<array<int,4>,4>>  allSG;

static int CELLS[9][2], NCELL;
static Sub TT[4][4]; static int INV[4];
static void recPG(int k){
    if(k==NCELL){ if(!assocHyper(TT)||!reversible(TT,INV)) return;
        array<array<Sub,4>,4> a{}; for(int i=0;i<N;i++)for(int j=0;j<N;j++)a[i][j]=TT[i][j];
        array<int,4> v{}; for(int i=0;i<N;i++)v[i]=INV[i];
        allPG.push_back(a); allPGinv.push_back(v); return; }
    int i=CELLS[k][0], j=CELLS[k][1]; bool hasE=(j==INV[i]);
    for(int mask=0; mask < (1<<(N-1)); mask++){
        Sub s=(Sub)((mask<<1)|(hasE?1:0)); if(!s) continue;
        TT[i][j]=s; if(partialOK(TT)) recPG(k+1); }
    TT[i][j]=0; }

int main(int argc,char**argv){
    N = argc>1? atoi(argv[1]) : 4;
    string outdir = argc>2? argv[2] : ".";
    initPerms();
    NCELL=0; for(int i=1;i<N;i++)for(int j=1;j<N;j++){CELLS[NCELL][0]=i;CELLS[NCELL][1]=j;NCELL++;}

    // ---- polygroups ----
    {   vector<array<int,4>> invs; array<int,4> id{}; for(int i=0;i<N;i++)id[i]=i; invs.push_back(id);
        for(int x=1;x<N;x++)for(int y=x+1;y<N;y++){ array<int,4> w=id; swap(w[x],w[y]); invs.push_back(w);}
        for(auto&iv:invs){ memset(TT,0,sizeof(TT));
            for(int x=0;x<N;x++){TT[0][x]=(Sub)(1<<x); TT[x][0]=(Sub)(1<<x);}
            for(int i=0;i<N;i++) INV[i]=iv[i]; recPG(0); } }

    map<uint64_t,int> pgMap; vector<int> pgRep; vector<int> pgAut;
    for(size_t z=0; z<allPG.size(); z++){
        Sub t[4][4]; for(int i=0;i<N;i++)for(int j=0;j<N;j++)t[i][j]=allPG[z][i][j];
        uint64_t best=~0ULL,id=keyPG(t); int ac=0;
        for(auto&p:PERM){ Sub o[4][4]; applyPG(t,p,o); uint64_t v=keyPG(o); best=min(best,v); if(v==id)ac++; }
        if(!pgMap.count(best)){ pgMap[best]=pgRep.size(); pgRep.push_back(z); pgAut.push_back(ac); } }
    vector<int> pgClassOf(allPG.size());
    for(size_t z=0; z<allPG.size(); z++){ Sub t[4][4]; for(int i=0;i<N;i++)for(int j=0;j<N;j++)t[i][j]=allPG[z][i][j];
        uint64_t best=~0ULL; for(auto&p:PERM){ Sub o[4][4]; applyPG(t,p,o); best=min(best,keyPG(o)); } pgClassOf[z]=pgMap[best]; }

    // ---- semigroups with x.e = e ----
    {   int m[4][4]; for(int i=0;i<N;i++) m[i][0]=0; int tot=N*(N-1);
        function<void(int)> rec=[&](int k){
            if(k==tot){ for(int i=0;i<N;i++)for(int j=0;j<N;j++)for(int l=0;l<N;l++)
                    if(m[m[i][j]][l]!=m[i][m[j][l]]) return;
                array<array<int,4>,4> a{}; for(int i=0;i<N;i++)for(int j=0;j<N;j++)a[i][j]=m[i][j];
                allSG.push_back(a); return; }
            int i=k/(N-1), j=k%(N-1)+1;
            for(int v=0;v<N;v++){ m[i][j]=v; rec(k+1); } m[i][j]=0; };
        rec(0); }
    map<uint64_t,int> sgMap; vector<int> sgRep, sgAut;
    for(size_t z=0;z<allSG.size();z++){ int m[4][4]; for(int i=0;i<N;i++)for(int j=0;j<N;j++)m[i][j]=allSG[z][i][j];
        uint64_t best=~0ULL,id=keySG(m); int ac=0;
        for(auto&p:PERM){ int o[4][4]; applySG(m,p,o); uint64_t v=keySG(o); best=min(best,v); if(v==id)ac++; }
        if(!sgMap.count(best)){ sgMap[best]=sgRep.size(); sgRep.push_back(z); sgAut.push_back(ac);} }
    vector<int> sgClassOf(allSG.size());
    for(size_t z=0;z<allSG.size();z++){ int m[4][4]; for(int i=0;i<N;i++)for(int j=0;j<N;j++)m[i][j]=allSG[z][i][j];
        uint64_t best=~0ULL; for(auto&p:PERM){ int o[4][4]; applySG(m,p,o); best=min(best,keySG(o)); } sgClassOf[z]=sgMap[best]; }

    auto leftDist=[&](const Sub t[4][4], const int m[4][4]){
        for(int a=0;a<N;a++)for(int b=0;b<N;b++)for(int c=0;c<N;c++){
            Sub L=0; for(int s=0;s<N;s++) if(t[b][c]>>s&1) L|=(Sub)(1<<m[a][s]);
            if(L!=t[m[a][b]][m[a][c]]) return false; } return true; };
    auto rightDist=[&](const Sub t[4][4], const int m[4][4]){
        for(int a=0;a<N;a++)for(int b=0;b<N;b++)for(int c=0;c<N;c++){
            Sub L=0; for(int s=0;s<N;s++) if(t[b][c]>>s&1) L|=(Sub)(1<<m[s][a]);
            if(L!=t[m[b][a]][m[c][a]]) return false; } return true; };

    // ---- composite structures ----
    struct Comp{ int pgz, sgz, aut; };
    map<uint64_t,int> hnrMap, hrMap, krMap;
    vector<Comp> hnr, hr, kr;         // hr = "hyperring" (bilateral 0 + both distrib); kr = Krasner (hr + canonical +)
    long long hnrLab=0, hrLab=0, krLab=0;
    // fertility / universality, counted on ISOMORPHISM CLASSES
    vector<set<int>> fertHNR(pgRep.size()), fertHR(pgRep.size());
    vector<set<int>> univHNR(sgRep.size()), univHR(sgRep.size());

    for(size_t pz=0; pz<allPG.size(); pz++){
        Sub t[4][4]; for(int i=0;i<N;i++)for(int j=0;j<N;j++)t[i][j]=allPG[pz][i][j];
        bool addComm=true; for(int x=0;x<N;x++)for(int y=0;y<N;y++) if(t[x][y]!=t[y][x]) addComm=false;
        for(size_t sz=0; sz<allSG.size(); sz++){
            int m[4][4]; for(int i=0;i<N;i++)for(int j=0;j<N;j++)m[i][j]=allSG[sz][i][j];
            if(!leftDist(t,m)) continue;
            hnrLab++;
            uint64_t best=~0ULL,id=(keyPG(t)<<24)|keySG(m); int ac=0;
            for(auto&p:PERM){ Sub o[4][4]; int q[4][4]; applyPG(t,p,o); applySG(m,p,q);
                uint64_t v=(keyPG(o)<<24)|keySG(q); best=min(best,v); if(v==id)ac++; }
            if(!hnrMap.count(best)){ hnrMap[best]=hnr.size(); hnr.push_back({(int)pz,(int)sz,ac}); }
            fertHNR[pgClassOf[pz]].insert(sgClassOf[sz]);
            univHNR[sgClassOf[sz]].insert(pgClassOf[pz]);
            bool absorb=true; for(int x=0;x<N;x++) if(m[0][x]!=0||m[x][0]!=0) absorb=false;
            if(absorb && rightDist(t,m)){
                hrLab++;
                if(!hrMap.count(best)){ hrMap[best]=hr.size(); hr.push_back({(int)pz,(int)sz,ac}); }
                fertHR[pgClassOf[pz]].insert(sgClassOf[sz]);
                univHR[sgClassOf[sz]].insert(pgClassOf[pz]);
                if(addComm){ krLab++; if(!krMap.count(best)){ krMap[best]=kr.size(); kr.push_back({(int)pz,(int)sz,ac}); } }
            } } }

    // ---------------- reporting ----------------
    printf("=========== ORDER n = %d ===========\n",N);
    printf("Polygroups      : labeled %5zu   classes %4zu\n", allPG.size(), pgRep.size());
    printf("Semigroups(x0=0): labeled %5zu   classes %4zu\n", allSG.size(), sgRep.size());
    printf("Hypernearrings  : labeled %5lld   classes %4zu\n", hnrLab, hnr.size());
    printf("Hyperrings*     : labeled %5lld   classes %4zu   (* 0 bilaterally absorbing + both distributive laws)\n", hrLab, hr.size());
    printf("Krasner hyperr. : labeled %5lld   classes %4zu   (additive canonical hypergroup)\n", krLab, kr.size());

    auto dumpStats=[&](const char* nm, vector<Comp>&v){
        map<int,int> ad; map<string,int> fgA, fgB; int mc=0, ac2=0;
        for(auto&c:v){ ad[c.aut]++;
            Sub t[4][4]; int m[4][4];
            for(int i=0;i<N;i++)for(int j=0;j<N;j++){t[i][j]=allPG[c.pgz][i][j]; m[i][j]=allSG[c.sgz][i][j];}
            bool com=true; for(int x=0;x<N;x++)for(int y=0;y<N;y++) if(m[x][y]!=m[y][x])com=false; if(com)mc++;
            bool ad2=true; for(int x=0;x<N;x++)for(int y=0;y<N;y++) if(t[x][y]!=t[y][x])ad2=false; if(ad2)ac2++;
            array<array<Sub,4>,4> A{},B{};
            for(int x=0;x<N;x++)for(int y=0;y<N;y++){A[x][y]=t[x][y]; B[x][y]=(Sub)(1<<m[x][y]);}
            int cls[4]; betaStar({A},cls); fgA[quotientGroup(t,cls)]++;
            betaStar({A,B},cls); fgB[quotientGroup(t,cls)]++; }
        printf("  %s : Aut", nm); for(auto&p:ad) printf(" %s:%d",autName(p.first).c_str(),p.second);
        printf(" | mult-comm %d | add-comm %d\n    beta*_PG :",mc,ac2);
        for(auto&p:fgA) printf(" %s:%d",p.first.c_str(),p.second);
        printf("\n    beta*_HNR:"); for(auto&p:fgB) printf(" %s:%d",p.first.c_str(),p.second); printf("\n"); };
    dumpStats("HNR",hnr); dumpStats("HR ",hr); dumpStats("KR ",kr);

    // polygroup detail + cross-tab
    { map<pair<int,string>,int> cross; map<string,int> fgd; map<int,int> autd; int comm=0, ncomm_rigid=0, ncomm=0;
      for(size_t i=0;i<pgRep.size();i++){
        Sub t[4][4]; for(int x=0;x<N;x++)for(int y=0;y<N;y++) t[x][y]=allPG[pgRep[i]][x][y];
        bool c=true; for(int x=0;x<N;x++)for(int y=0;y<N;y++) if(t[x][y]!=t[y][x])c=false;
        if(c)comm++; else { ncomm++; if(pgAut[i]==1) ncomm_rigid++; }
        array<array<Sub,4>,4> A{}; for(int x=0;x<N;x++)for(int y=0;y<N;y++)A[x][y]=t[x][y];
        int cls[4]; betaStar({A},cls); string fg=quotientGroup(t,cls);
        fgd[fg]++; autd[pgAut[i]]++; cross[{pgAut[i],fg}]++; }
      printf("  POLYGROUPS: commutative %d | non-commutative %d (rigid: %d)\n",comm,ncomm,ncomm_rigid);
      printf("    fundamental groups:"); for(auto&p:fgd) printf(" %s:%d",p.first.c_str(),p.second);
      printf("\n    Aut:"); for(auto&p:autd) printf(" %s:%d",autName(p.first).c_str(),p.second);
      printf("\n    cross-tab Aut x P/beta*:\n");
      for(auto&p:cross) printf("      Aut=%-2s  P/beta*=%-6s : %d\n",autName(p.first.first).c_str(),p.first.second.c_str(),p.second); }

    // barren counts
    { int bH=0,bR=0; for(size_t i=0;i<sgRep.size();i++){ if(univHNR[i].empty())bH++; if(univHR[i].empty())bR++; }
      int pH=0,pR=0; for(size_t i=0;i<pgRep.size();i++){ if(fertHNR[i].empty())pH++; if(fertHR[i].empty())pR++; }
      printf("  BARREN: semigroups %d/%zu (HNR), %d/%zu (HR) | polygroups %d, %d\n",bH,sgRep.size(),bR,sgRep.size(),pH,pR); }

    // ---------------- CSV output ----------------
    auto canonTabPG=[&](const Sub t[4][4], Sub out[4][4]){ string b; Sub bb[4][4];
        for(auto&p:PERM){ Sub o[4][4]; applyPG(t,p,o); string c=codePGraw(o); if(b.empty()||c<b){b=c; memcpy(bb,o,sizeof(bb));} }
        memcpy(out,bb,sizeof(bb)); };
    auto canonTabSG=[&](const int m[4][4], int out[4][4]){ string b; int bb[4][4];
        for(auto&p:PERM){ int o[4][4]; applySG(m,p,o); string c=codeSGraw(o); if(b.empty()||c<b){b=c; memcpy(bb,o,sizeof(bb));} }
        memcpy(out,bb,sizeof(bb)); };
    auto tableStrPG=[&](const Sub t[4][4]){ string s; for(int i=0;i<N;i++){ for(int j=0;j<N;j++){ s+=hexchar(t[i][j]); } if(i<N-1)s+="|"; } return s; };
    auto tableStrSG=[&](const int m[4][4]){ string s; for(int i=0;i<N;i++){ for(int j=0;j<N;j++) s+=hexchar(m[i][j]); if(i<N-1)s+="|"; } return s; };
    char buf[512];
    { snprintf(buf,sizeof buf,"%s/polygroups_n%d.csv",outdir.c_str(),N); FILE*f=fopen(buf,"w");
      fprintf(f,"id,code,table,inverse_map,commutative,aut_order,aut_structure,fundamental_group,fertility_hnr,fertility_hr\n");
      for(size_t i=0;i<pgRep.size();i++){ int z=pgRep[i];
        Sub t[4][4]; for(int x=0;x<N;x++)for(int y=0;y<N;y++) t[x][y]=allPG[z][x][y];
        bool c=true; for(int x=0;x<N;x++)for(int y=0;y<N;y++) if(t[x][y]!=t[y][x])c=false;
        string iv; for(int x=0;x<N;x++) iv+=hexchar(allPGinv[z][x]);
        array<array<Sub,4>,4> A{}; for(int x=0;x<N;x++)for(int y=0;y<N;y++)A[x][y]=t[x][y];
        int cls[4]; betaStar({A},cls);
        Sub ct[4][4]; canonTabPG(t,ct);
        fprintf(f,"PG_%zu,%s,%s,%s,%d,%d,%s,%s,%zu,%zu\n",i+1,codePG(t).c_str(),tableStrPG(ct).c_str(),iv.c_str(),
                c?1:0,pgAut[i],autName(pgAut[i]).c_str(),quotientGroup(t,cls).c_str(),fertHNR[i].size(),fertHR[i].size()); }
      fclose(f); }
    { snprintf(buf,sizeof buf,"%s/semigroups_n%d.csv",outdir.c_str(),N); FILE*f=fopen(buf,"w");
      fprintf(f,"id,code,table,commutative,aut_order,aut_structure,universality_hnr,universality_hr,barren_hnr,barren_hr\n");
      for(size_t i=0;i<sgRep.size();i++){ int z=sgRep[i];
        int m[4][4]; for(int x=0;x<N;x++)for(int y=0;y<N;y++) m[x][y]=allSG[z][x][y];
        bool c=true; for(int x=0;x<N;x++)for(int y=0;y<N;y++) if(m[x][y]!=m[y][x])c=false;
        int cm[4][4]; canonTabSG(m,cm);
        fprintf(f,"SG_%zu,%s,%s,%d,%d,%s,%zu,%zu,%d,%d\n",i+1,codeSG(m).c_str(),tableStrSG(cm).c_str(),c?1:0,
                sgAut[i],autName(sgAut[i]).c_str(),univHNR[i].size(),univHR[i].size(),
                univHNR[i].empty()?1:0, univHR[i].empty()?1:0); }
      fclose(f); }
    auto dumpComp=[&](const char*fn, vector<Comp>&v, const char*pre){
        snprintf(buf,sizeof buf,"%s/%s_n%d.csv",outdir.c_str(),fn,N); FILE*f=fopen(buf,"w");
        fprintf(f,"id,polygroup_id,semigroup_id,add_code,mult_code,add_table,mult_table,add_commutative,mult_commutative,aut_order,aut_structure,fund_group_additive,fund_group_full\n");
        for(size_t i=0;i<v.size();i++){ auto&c=v[i];
            Sub t0[4][4]; int m0[4][4];
            for(int x=0;x<N;x++)for(int y=0;y<N;y++){t0[x][y]=allPG[c.pgz][x][y]; m0[x][y]=allSG[c.sgz][x][y];}
            // canonicalise the PAIR: the same permutation is applied to both tables
            Sub t[4][4]; int m[4][4]; string bestkey;
            for(auto&p:PERM){ Sub o[4][4]; int q[4][4]; applyPG(t0,p,o); applySG(m0,p,q);
                string kk=codePGraw(o)+"|"+codeSGraw(q);
                if(bestkey.empty()||kk<bestkey){ bestkey=kk; memcpy(t,o,sizeof(t)); memcpy(m,q,sizeof(m)); } }
            bool ac=true; for(int x=0;x<N;x++)for(int y=0;y<N;y++) if(t[x][y]!=t[y][x])ac=false;
            bool mc=true; for(int x=0;x<N;x++)for(int y=0;y<N;y++) if(m[x][y]!=m[y][x])mc=false;
            array<array<Sub,4>,4> A{},B{};
            for(int x=0;x<N;x++)for(int y=0;y<N;y++){A[x][y]=t[x][y]; B[x][y]=(Sub)(1<<m[x][y]);}
            int cls[4]; betaStar({A},cls); string f1=quotientGroup(t,cls);
            betaStar({A,B},cls); string f2=quotientGroup(t,cls);
            fprintf(f,"%s_%zu,PG_%d,SG_%d,%s,%s,%s,%s,%d,%d,%d,%s,%s,%s\n",pre,i+1,
                pgClassOf[c.pgz]+1,sgClassOf[c.sgz]+1,codePGraw(t).c_str(),codeSGraw(m).c_str(),
                tableStrPG(t).c_str(),tableStrSG(m).c_str(),ac?1:0,mc?1:0,c.aut,autName(c.aut).c_str(),f1.c_str(),f2.c_str()); }
        fclose(f); };
    dumpComp("hypernearrings",hnr,"HNR"); dumpComp("hyperrings",hr,"HR"); dumpComp("krasner_hyperrings",kr,"KR");
    printf("CSV files written to %s\n",outdir.c_str());
    return 0;
}
