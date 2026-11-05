var G={k:"♚",q:"♛",r:"♜",b:"♝",n:"♞",p:"♟"},TX="\uFE0E",V={p:100,n:320,b:330,r:500,q:900,k:0},L={k:"R",q:"D",r:"T",b:"A",n:"C"},FL="abcdefgh";
var DN=[[1,2],[2,1],[-1,2],[-2,1],[1,-2],[2,-1],[-1,-2],[-2,-1]],DK=[[1,0],[-1,0],[0,1],[0,-1],[1,1],[1,-1],[-1,1],[-1,-1]];
var S,hist,ks,sel,mv,pend,LG,over,res,ai=true,lv=2,flip=false,mode="play",tool="P",note="",eb,etm="w";
var $=function(id){return document.getElementById(id)};
function wh(p){return p===p.toUpperCase()}
function ok(r,c){return r>=0&&r<8&&c>=0&&c<8}
function fen(){var b=[];"rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR".split("").forEach(function(ch){if(ch==="/")return;if(/\d/.test(ch)){for(var k=0;k<+ch;k++)b.push("")}else b.push(ch)});return b}
function kidx(b,w){return b.indexOf(w?"K":"k")}
function att(b,sq,w){
 var r=sq>>3,c=sq&7,i,d,rr,cc,p,pr=w?r+1:r-1;
 for(i=-1;i<2;i+=2){cc=c+i;if(ok(pr,cc)&&b[pr*8+cc]===(w?"P":"p"))return true}
 for(i=0;i<8;i++){rr=r+DN[i][0];cc=c+DN[i][1];if(ok(rr,cc)&&b[rr*8+cc]===(w?"N":"n"))return true;
  rr=r+DK[i][0];cc=c+DK[i][1];if(ok(rr,cc)&&b[rr*8+cc]===(w?"K":"k"))return true}
 for(i=0;i<8;i++){d=DK[i];var x=i>3?(w?"B":"b"):(w?"R":"r");rr=r+d[0];cc=c+d[1];
  while(ok(rr,cc)){p=b[rr*8+cc];if(p){if(p===x||p===(w?"Q":"q"))return true;break}rr+=d[0];cc+=d[1]}}
 return false}
function inCheck(s){return att(s.b,kidx(s.b,s.t==="w"),s.t!=="w")}
function gen(s){
 var b=s.b,w=s.t==="w",m=[];
 function add(f,t,x){var o={f:f,t:t};if(x)for(var k in x)o[k]=x[k];m.push(o)}
 function pm(f,t,pr){if(pr)["q","r","b","n"].forEach(function(l){add(f,t,{p:l})});else add(f,t)}
 for(var i=0;i<64;i++){
  var p=b[i];if(!p||wh(p)!==w)continue;
  var r=i>>3,c=i&7,t=p.toLowerCase();
  if(t==="p"){
   var d=w?-1:1,r1=r+d,pr=r1===(w?0:7);
   if(!b[r1*8+c]){pm(i,r1*8+c,pr);if(r===(w?6:1)&&!b[(r+2*d)*8+c])add(i,(r+2*d)*8+c)}
   [-1,1].forEach(function(dc){var cc=c+dc;if(cc<0||cc>7)return;var to=r1*8+cc,q=b[to];
    if(q&&wh(q)!==w)pm(i,to,pr);else if(!q&&to===s.ep)add(i,to,{e:1})});
  }else{
   var dirs=t==="n"?DN:t==="b"?DK.slice(4):t==="r"?DK.slice(0,4):DK,sl=t==="b"||t==="r"||t==="q";
   dirs.forEach(function(dd){var rr=r+dd[0],cc=c+dd[1];
    while(ok(rr,cc)){var q=b[rr*8+cc];if(!q)add(i,rr*8+cc);else{if(wh(q)!==w)add(i,rr*8+cc);break}
     if(!sl)break;rr+=dd[0];cc+=dd[1]}});
   if(t==="k"&&i===(w?60:4)){
    var o=w?56:0,R=w?"R":"r";
    if(s.c.indexOf(w?"K":"k")>=0&&b[o+7]===R&&!b[o+5]&&!b[o+6]&&!att(b,o+4,!w)&&!att(b,o+5,!w))add(i,o+6,{k:1});
    if(s.c.indexOf(w?"Q":"q")>=0&&b[o]===R&&!b[o+1]&&!b[o+2]&&!b[o+3]&&!att(b,o+4,!w)&&!att(b,o+3,!w))add(i,o+2,{k:1});
   }
  }
 }
 return m}
var RT={60:"KQ",63:"K",56:"Q",4:"kq",7:"k",0:"q"};
function apply(s,m){
 var b=s.b.slice(),p=b[m.f],w=s.t==="w",cap=b[m.t]||m.e,c=s.c,ep=-1;
 b[m.t]=p;b[m.f]="";
 if(m.e)b[m.t+(w?8:-8)]="";
 if(m.k){var o=m.t>m.f?m.t+1:m.t-2,d=m.t>m.f?m.t-1:m.t+1;b[d]=b[o];b[o]=""}
 if(m.p)b[m.t]=w?m.p.toUpperCase():m.p;
 if(p.toLowerCase()==="p"&&Math.abs(m.t-m.f)===16)ep=(m.f+m.t)/2;
 [m.f,m.t].forEach(function(q){var x=RT[q];if(x)for(var j=0;j<x.length;j++)c=c.replace(x[j],"")});
 return{b:b,t:w?"b":"w",c:c,ep:ep,hm:(cap||p.toLowerCase()==="p")?0:s.hm+1}}
function legal(s){var w=s.t==="w";return gen(s).filter(function(m){var n=apply(s,m);return !att(n.b,kidx(n.b,w),!w)})}
function key(s){return s.b.join("")+s.t+s.c+s.ep}
function insuf(b){var o=b.filter(function(p){return p&&p.toLowerCase()!=="k"});return !o.length||(o.length===1&&/[bn]/i.test(o[0]))}
function ev(b){var x=0;for(var i=0;i<64;i++){var p=b[i];if(!p)continue;var t=p.toLowerCase(),r=i>>3,c=i&7,v=V[t],
 cen=(7-Math.abs(r-3.5)-Math.abs(c-3.5))*(t==="n"||t==="b"?5:t==="p"?3:0);if(t==="p")cen+=(wh(p)?6-r:r-1)*5;x+=wh(p)?v+cen:-(v+cen)}return x}
function nm(s,d,a,b){
 if(d===0)return ev(s.b)*(s.t==="w"?1:-1);
 var ls=legal(s);if(!ls.length)return inCheck(s)?-99999-d:0;
 var sc=function(m){return(s.b[m.t]?V[s.b[m.t].toLowerCase()]:0)+(m.p?800:0)};
 ls.sort(function(x,y){return sc(y)-sc(x)});
 for(var i=0;i<ls.length;i++){var v=-nm(apply(s,ls[i]),d-1,-b,-a);if(v>a)a=v;if(a>=b)break}
 return a}
function aiMove(){
 if(mode!=="play"||S.t!=="b"||over)return;
 var best=null,bs=-1e9;
 LG.forEach(function(m){var v=-nm(apply(S,m),lv-1,-1e9,1e9)+Math.random()*(lv===1?70:3);if(v>bs){bs=v;best=m}});
 if(best)play(best)}
function refresh(){
 LG=legal(S);S.chk=inCheck(S);over=false;res="";
 if(!LG.length){over=true;res=S.chk?"Jaque mate · ganan "+(S.t==="w"?"negras":"blancas"):"Tablas por ahogado"}
 else if(S.hm>=100){over=true;res="Tablas por la regla de 50 movimientos"}
 else if(insuf(S.b)){over=true;res="Tablas por material insuficiente"}
 else if(ks.filter(function(k){return k===key(S)}).length>=3){over=true;res="Tablas por triple repetición"}}
function san(s,m){
 var p=s.b[m.f],t=p.toLowerCase(),f=function(i){return FL[i&7]+(8-(i>>3))};
 if(m.k)return m.t>m.f?"O-O":"O-O-O";
 var cp=s.b[m.t]||m.e,o="";
 if(t==="p")o=(cp?FL[m.f&7]+"x":"")+f(m.t)+(m.p?"="+L[m.p]:"");
 else{o=L[t];var oth=LG.filter(function(x){return x.t===m.t&&x.f!==m.f&&s.b[x.f]===p});
  if(oth.length)o+=oth.some(function(x){return(x.f&7)===(m.f&7)})?(8-(m.f>>3)):FL[m.f&7];
  o+=(cp?"x":"")+f(m.t)}
 return o}
function play(m){
 var ns=apply(S,m),n=san(S,m);hist.push({s:S,m:m,n:n});S=ns;ks.push(key(S));sel=null;mv=[];pend=null;refresh();
 var h=hist[hist.length-1];if(res.indexOf("Jaque mate")===0)h.n+="#";else if(S.chk)h.n+="+";
 window.anim=[{f:m.f,t:m.t}];if(m.k)window.anim.push({f:m.t>m.f?m.t+1:m.t-2,t:m.t>m.f?m.t-1:m.t+1});render();if(ai&&S.t==="b"&&!over)setTimeout(aiMove,350)}
function newGame(){S={b:fen(),t:"w",c:"KQkq",ep:-1,hm:0};hist=[];ks=[key(S)];sel=null;mv=[];pend=null;refresh();render()}
function glyph(p){return'<span class="'+(wh(p)?"w":"k")+'">'+G[p.toLowerCase()]+TX+"</span>"}
var cells=[];
for(var j=0;j<64;j++){(function(j){var d=document.createElement("div");d.onclick=function(){tap(flip?63-j:j)};$("b").appendChild(d);cells.push(d)})(j)}
var pal=$("pal");
"KQRBNPkqrbnpx".split("").forEach(function(t){var b=document.createElement("button");b.dataset.t=t;
 if(t==="x"){b.textContent="Borrar pieza";b.className="x"}else b.innerHTML=glyph(t);
 b.onclick=function(){tool=t;note="";render()};pal.appendChild(b)});
function render(){
 var b=mode==="edit"?eb:S.b,ki=-1,txt;
 if(mode==="play"){
  txt=over?res:(ai?(S.t==="w"?"Tu turno (blancas)":"Piensa el ordenador…"):"Mueven "+(S.t==="w"?"blancas":"negras"))+(S.chk?" · jaque":"");
  if(S.chk)ki=kidx(S.b,S.t==="w");
 }else txt=note||(tool==="x"?"Toca una pieza para borrarla":"Toca una casilla para colocar la pieza");
 $("st").innerHTML=(mode==="play"&&!over?'<i class="dt '+(S.t==="w"?"dw":"db")+'"></i>':"")+txt;
 cells.forEach(function(c,j){
  var i=flip?63-j:j,p=b[i],cl="q "+(((i>>3)+(i&7))%2?"d":"l"),h=p?glyph(p):"";
  if(mode==="play"){var l=hist.length?hist[hist.length-1].m:null;
   if(l&&(i===l.f||i===l.t))cl+=" last";if(i===sel)cl+=" sel";if(i===ki)cl+=" chk";
   if(mv.some(function(m){return m.t===i}))cl+=" ok"+(p||(S.b[sel]&&/p/i.test(S.b[sel])&&(i&7)!==(sel&7))?" cap":"")}
  if(j%8===0)h+='<i class="r">'+(8-(i>>3))+"</i>";
  if(j>55)h+='<i class="f">'+FL[i&7]+"</i>";
  c.className=cl;c.innerHTML=h});
 if(window.anim&&mode==="play"){var w0=cells[0].offsetWidth;window.anim.forEach(function(a){
  var jf=flip?63-a.f:a.f,jt=flip?63-a.t:a.t,e=cells[jt].querySelector("span");if(!e)return;
  e.style.position="relative";e.style.zIndex=5;e.style.transition="none";
  e.style.transform="translate("+(((jf&7)-(jt&7))*w0)+"px,"+(((jf>>3)-(jt>>3))*w0)+"px)";
  e.offsetWidth;e.style.transition="transform .28s ease";e.style.transform="translate(0,0)"});window.anim=null}
 Array.prototype.forEach.call(pal.children,function(x){x.setAttribute("aria-pressed",x.dataset.t===tool)});
 $("mw").textContent="Mueven: "+(etm==="w"?"blancas":"negras");
 $("md").textContent=ai?"vs. ordenador":"2 jugadores";
 $("lv").textContent="Nivel: "+["","Fácil","Medio","Difícil"][lv];$("lv").classList.toggle("hide",!ai);
 var pr=$("pr");pr.classList.toggle("hide",!pend);
 if(pend){pr.innerHTML="Corona a:";pend.forEach(function(m){var x=document.createElement("button"),pc=S.t==="w"?m.p.toUpperCase():m.p;x.innerHTML=glyph(pc);x.onclick=function(){play(m)};pr.appendChild(x)})}
 if(mode==="play"){
  var cap=function(w){var n={p:0,n:0,b:0,r:0,q:0},I={p:8,n:2,b:2,r:2,q:1},s="",v=0;
   S.b.forEach(function(p){if(p&&wh(p)===w&&p.toLowerCase()!=="k")n[p.toLowerCase()]++});
   "qrbnp".split("").forEach(function(t){for(var k=n[t];k<I[t];k++){s+=glyph(w?t.toUpperCase():t);v+=V[t]/100}});return{s:s,v:v}};
  var cw=cap(false),cb=cap(true),d=Math.round(cw.v-cb.v);
  $("cp").innerHTML="<span><small>Blancas capturan</small> "+(cw.s||"–")+(d>0?" <small>+"+d+"</small>":"")+"</span><span>"+(cb.s||"–")+" <small>Negras capturan</small>"+(d<0?" <small>+"+(-d)+"</small>":"")+"</span>";
  var h="";hist.forEach(function(x,k){var n0=x.s.t==="w";if(n0||k===0)h+="<b>"+(Math.floor(k/2)+1)+(n0?".":"…")+"</b> ";h+=x.n+" "});
  $("mvl").innerHTML=h||"Las jugadas aparecerán aquí";$("mvl").scrollTop=1e5;
 }}
function tap(i){
 if(mode==="edit"){var r=i>>3;
  if(tool==="x"||eb[i]===tool)eb[i]="";
  else if(/p/i.test(tool)&&(r===0||r===7)){note="Los peones no pueden ir en la primera ni última fila";return render()}
  else eb[i]=tool;
  note="";return render()}
 if(over||pend||(ai&&S.t==="b"))return;
 var c=mv.filter(function(x){return x.t===i});
 if(c.length>1){pend=c;return render()}
 if(c.length)return play(c[0]);
 var p=S.b[i];
 if(p&&wh(p)===(S.t==="w")){sel=i;mv=LG.filter(function(x){return x.f===i})}else{sel=null;mv=[]}
 render()}
function setMode(m){mode=m;$("tp").setAttribute("aria-pressed",m==="play");$("te").setAttribute("aria-pressed",m==="edit");
 $("play").classList.toggle("hide",m!=="play");$("edit").classList.toggle("hide",m!=="edit");
 if(m==="edit"){eb=S.b.slice();etm=S.t;note="";sel=null;mv=[];pend=null}render()}
$("tp").onclick=function(){setMode("play")};$("te").onclick=function(){setMode("edit")};
$("nw").onclick=newGame;
$("un").onclick=function(){if(pend||(ai&&S.t==="b"&&!over))return;var n=(ai&&S.t==="w")?2:1;while(n--&&hist.length){S=hist.pop().s;ks.pop()}sel=null;mv=[];refresh();render()};
$("fl").onclick=function(){flip=!flip;render()};
$("md").onclick=function(){ai=!ai;newGame()};
$("lv").onclick=function(){lv=lv%3+1;render()};
$("mw").onclick=function(){etm=etm==="w"?"b":"w";render()};
$("ec").onclick=function(){eb=eb.map(function(){return ""});note="";render()};
$("ei").onclick=function(){eb=fen();etm="w";note="";render()};
$("go").onclick=function(){
 var wk=eb.filter(function(p){return p==="K"}).length,bk=eb.filter(function(p){return p==="k"}).length;
 if(wk!==1||bk!==1){note="Necesitas exactamente un rey blanco y uno negro";return render()}
 if(att(eb,kidx(eb,etm!=="w"),etm==="w")){note="Posición ilegal: el rey del bando que no mueve está en jaque";return render()}
 var c="";if(eb[60]==="K"&&eb[63]==="R")c+="K";if(eb[60]==="K"&&eb[56]==="R")c+="Q";if(eb[4]==="k"&&eb[7]==="r")c+="k";if(eb[4]==="k"&&eb[0]==="r")c+="q";
 S={b:eb.slice(),t:etm,c:c,ep:-1,hm:0};hist=[];ks=[key(S)];sel=null;mv=[];pend=null;refresh();setMode("play");
 if(ai&&S.t==="b"&&!over)setTimeout(aiMove,350)};
newGame();
