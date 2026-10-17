/* Config {F1,F26,E24,E27} at e=70 inside Z/M, M=70k: find y1,y2 (y1+y2 = -sum) making A balanced. */
#include <stdio.h>
#include <stdlib.h>
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){int k0=atoi(argv[1]),k1=atoi(argv[2]);
 for(int k=k0;k<=k1;k++){int M=70*k,g=M/70;int C[4]={g*1,g*61,g*24,g*62};long s=0;for(int i=0;i<4;i++)s+=C[i];int y12=(int)((-s%M+M)%M);
  int *U=malloc(sizeof(int)*M),nu=0;for(int t=1;t<M;t++)if(gcd(t,M)==1)U[nu++]=t;
  int cnt=0;
  for(int y1=1;y1<M;y1++){int y2=(y12-y1+M)%M;if(y2==0||y2<y1)continue;
   int ok=1;for(int i=0;i<nu&&ok;i++){long t=U[i],S=0;for(int j=0;j<4;j++)S+=(t*C[j])%M;S+=(t*y1)%M+(t*y2)%M;if(S!=3L*M)ok=0;}
   if(ok){cnt++;printf("M=%d y1=%d (ord %d) y2=%d (ord %d)\n",M,y1,M/gcd(y1,M),y2,M/gcd(y2,M));}}
  printf("M=%d solutions=%d\n",M,cnt);free(U);}
 return 0;}
