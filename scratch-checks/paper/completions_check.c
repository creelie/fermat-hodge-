/* Independent check: each multiset of four elements below is balanced at its
   level N: sum 0 mod N, no zero entry, and sum of <t a> equals 2N for every unit t. */
#include <stdio.h>
static int g(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int main(void){
  int rows[13][5]={{30,1,19,25,15},{30,1,24,20,15},{60,1,49,40,30},{15,1,6,13,10},
   {20,1,12,17,10},{30,1,7,27,25},{60,2,21,57,40},{28,1,9,25,21},{42,1,24,38,21},
   {42,1,25,37,21},{42,1,30,32,21},{66,1,25,62,44},{78,1,55,61,39}};
  int bad=0;
  for(int r=0;r<13;r++){int N=rows[r][0],s=0,ok=1;
    for(int i=1;i<5;i++){s+=rows[r][i]; if(rows[r][i]%N==0) ok=0;}
    if(s%N) ok=0;
    for(int t=1;t<N;t++) if(g(t,N)==1){int h=0; for(int i=1;i<5;i++) h+=(t*rows[r][i])%N; if(h!=2*N) ok=0;}
    printf("N=%d {%d,%d,%d,%d} %s\n",N,rows[r][1],rows[r][2],rows[r][3],rows[r][4],ok?"balanced":"NOT");
    bad+=!ok;}
  printf("failures: %d\n",bad); return bad;}
