import{mkdirSync as a,readdirSync as b,readFileSync as c,writeFileSync as d}from'node:fs';
let W;
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output',D=[[0,-1,'u'],[0,1,'d'],[-1,0,'l'],[1,0,'r']],$=(x,y)=>x-y;
function P(t){let r=t.split('\n').filter(x=>x),h=r.length,w=Math.max(...r.map(x=>x.length)),a=new Uint8Array(w*h).fill(1),g=[],b=[],p=-1;
W=[-w,w,-1,1];
r.forEach((s,y)=>{for(let x=0;x<s.length;x++){let c=s[x],i=y*w+x;if(c=='#')continue;if(x&&y&&x<w-1&&y<h-1)a[i]=0;if('.*+'.includes(c))g.push(i);if('$*'.includes(c))b.push(i);if('@+'.includes(c))p=i}});
return[w,h,a,g,b.sort($),p]}
function Q(L,f){let[w,,a]=L,d=Array(a.length).fill(-1),q=[f];d[f]=0;
for(let i=0;i<q.length;i++){let p=q[i];for(let e of W){let n=p+e;if(!a[n]&&d[n]<0){d[n]=d[p]+1;q.push(n)}}}return d}
function V(L){let[w,,a,G]=L,v=Array(a.length).fill(0),q=G.map(g=>(v[g]=1,g));
for(let i=0;i<q.length;i++){let x=q[i];for(let e of W){let y=x-e;if(!a[y]&&!a[y-e]&&!v[y]){v[y]=1;q.push(y)}}}return v}
function E(L){let[w,,a,G]=L,s=a.length,d=Array(s).fill(0),m=[...d];
for(let g of G)m[g]=1;
for(let e of W){let p=e%w?w:1;
for(let i=0;i<s;i++){if(a[i]||!a[i+e]||m[i])continue;let g=0,x=0,c=i;while(!a[c-p])c-=p;
for(;!a[c];c+=p){if(m[c])g=1;if(!a[c+e])x=1}
if(!g&&!x)d[i]=1}}return d}
function C(L,o,f,s,t,k){let[w,,a]=L,v=f,n=0;k[n++]=f;s[f]=t;
while(n){let p=k[--n];if(p<v)v=p;
for(let e of W){let q=p+e;if(!a[q]&&!o[q]&&s[q]!=t){s[q]=t;k[n++]=q}}}return v}
function F(L,o,m,t){let[w,,a]=L,B=x=>a[x]|o[x],N=x=>o[x]&!m[x];
for(let u of[t,t-1,t-w,t-w-1])if(B(u)&B(u+1)&B(u+w)&B(u+w+1)&&(N(u)|N(u+1)|N(u+w)|N(u+w+1)))return!0;
return!1}
function Z(L,m,B){let[w,,a]=L,f=Array(a.length).fill(0),c=1;
while(c){c=0;
for(let b of B){if(f[b])continue;if(!W.some(e=>!a[b+e]&&!f[b+e]&&!a[b-e]&&!f[b-e])){f[b]=1;c=1}}}
return B.some(b=>f[b]&&!m[b])}
function T(L,o,f,t){let[w,,a]=L;
if(f==t)return'';
let v=Array(a.length).fill(-1),h=[],q=[f];v[f]=f;
for(let i=0;i<q.length;i++){let p=q[i];if(p==t)break;
for(let[dx,dy,l]of D){let n=p+dy*w+dx;if(a[n]||o[n]||v[n]!=-1)continue;v[n]=p;h[n]=l;q.push(n)}}
if(v[t]<0)throw 0;
let s='';for(let p=t;p!=f;p=v[p])s=h[p]+s;return s}
function S(L,X){let[w,,a,G,Y,K]=L,s=a.length,n=Y.length,m=Array(s).fill(0);
for(let g of G)m[g]=1;
let v=V(L),e=E(L),O=b=>b.every(x=>m[x]);
if(Y.some(b=>!v[b]))return null;
let d=G.map(g=>Q(L,g));
let H=b=>{let A=1/0;
let r=(i,c,k)=>{if(c>=A)return;if(i==b.length)return A=c;
for(let g=0;g<n;g++){if(k>>g&1)continue;let y=d[g][b[i]];if(y<0)continue;r(i+1,c+y,k|1<<g)}};r(0,0,0);return A};
let J=(b,l)=>{let q=l;for(let x of b)q=q*s+x;return q};
let A2=[[Y.slice(),K,0,-1,0,0]],A=new Map,o=Array(s).fill(0),y=[...o],j=[...o],q=Array(s),t=0;
for(let b of Y)o[b]=1;
A2[0][2]=C(L,o,K,y,++t,q);
for(let b of Y)o[b]=0;
A.set(J(Y,A2[0][2]),0);
let bk=[],cf=0,cn=0;
let pu=(f,i)=>{(bk[f]??=[]).push(i);cn++};
let po=()=>{while(!bk[cf]?.length)cf++;cn--;return bk[cf].pop()};
pu(H(Y),0);
let e2=0,f=-1;
while(cn){let x=po(),st=A2[x],b=st[0],g2=st[5];
if(A.get(J(b,st[2]))!==g2)continue;
if(O(b)){f=x;break}
if(e2>=X)return null;
e2++;
for(let z of b)o[z]=1;
C(L,o,st[1],y,++t,q);
let he=t;
for(let i=0;i<n&&f<0;i++){let z=b[i];
for(let dd of W){let t3=z+dd;
if(a[t3]||o[t3]||!v[t3]||e[t3])continue;
if(y[z-dd]!==he)continue;
let N2=b.slice();N2[i]=t3;N2.sort($);
o[z]=0;o[t3]=1;
let D2=F(L,o,m,t3)||Z(L,m,N2),l=0,K2='';
if(!D2){l=C(L,o,z,j,++t,q);K2=J(N2,l)}
o[t3]=0;o[z]=1;
if(D2)continue;
let g3=g2+1,K3=A.get(K2);
if(K3!==undefined&&K3<=g3)continue;
A.set(K2,g3);
let idx=A2.length;
A2.push([N2,z,l,x,t3,g3]);
pu(g3+H(N2),idx);}}
for(let z of b)o[z]=0}
if(f<0)return null;
let r=[];for(let i=f;i>0;i=A2[i][3])r.unshift(i);
let mv='',P3=K,b3=Y.slice();
for(let i of r){let st=A2[i],f3=st[1],t3=st[4],d=t3-f3;
for(let b of b3)o[b]=1;
mv+=T(L,o,P3,f3-d);
for(let b of b3)o[b]=0;
mv+='UDLR'[W.indexOf(d)];
P3=f3;b3=b3.map(b=>b==f3?t3:b)}
return{m:mv,P:A2[f][1]}}
function U(L){let[w,,a,G,B,p]=L,v=V(L),r=(p/w)|0,c=[];
for(let i=r*w;i<(r+1)*w;i++)if(!a[i]&&!v[i])c[i]=1;
if(B.some(b=>c[b]))return null;
let t=Array(a.length).fill(-1),R=[];
for(let s=0;s<a.length;s++){if(a[s]||c[s]||t[s]>=0)continue;
let q=[s];t[s]=R.length;
for(let i=0;i<q.length;i++)for(let e of W){let n=q[i]+e;if(!a[n]&&!c[n]&&t[n]<0){t[n]=R.length;q.push(n)}}
R.push({b:[],g:[],d:!1})}
for(let b of B)R[t[b]].b.push(b);
for(let g of G){if(t[g]<0)return null;R[t[g]].g.push(g)}
if(R.some(x=>x.b.length!=x.g.length))return null;
return R.filter(x=>x.b.length)}
function G(L){let R=U(L);if(!R)return null;
let p=L[5],m='';
for(let r of R){let a=L[2].slice();
for(let o of R){if(o==r)continue;for(let b of o.d?o.g:o.b)a[b]=1}
let v=[L[0],L[1],a,r.g,r.b,p],z=S(v,8e5);
if(!z)return null;
m+=z.m;p=z.P;
r.d=!0}
return{m}}
function Y(t){let L=P(t);return(G(L)||{m:''}).m}
for(let i of b(I).sort()){let m='';try{m=Y(c(I+'/'+i+'/level.txt','utf8'))}catch{m=''}a(O+'/'+i,{recursive:true});d(O+'/'+i+'/solution.txt',m+'\n')}
