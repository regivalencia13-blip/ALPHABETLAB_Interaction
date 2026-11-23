'use strict';
const stage=document.querySelector('#stage'),ctx=stage.getContext('2d'),host=document.querySelector('#engines');
const palettes={amoeba:'#c3c6c7',fungi:'#a5b89a',bacteria:'#72a6bc',protozoa:'#d28fa0'};
let bacteriaType='A';
let amoebaSchedule={grow:6.5,hold:2.75,recover:8};
let species='fungi',text='HELLO',engines=new Map(),active=[],generation=0,clock=3,last=0,paint=0,speed=.65,density=.8,ready=false;
const status=document.querySelector('#live-status');
let printing=false,receiptCachedAt=0;
function crop(canvas){const c=canvas.getContext('2d'),{width:w,height:h}=canvas,d=c.getImageData(0,0,w,h).data;let x=w,y=h,r=0,b=0;for(let j=0;j<h;j++)for(let i=0;i<w;i++){const k=(j*w+i)*4;if(d[k+3]>90&&Math.max(d[k],d[k+1],d[k+2])>100){x=Math.min(x,i);y=Math.min(y,j);r=Math.max(r,i);b=Math.max(b,j)}}return r>x?{x:Math.max(0,x-5),y:Math.max(0,y-5),w:r-x+11,h:b-y+11}:{x:0,y:0,w,h};}
function coreCrop(canvas){
 const {width:w,height:h}=canvas,d=canvas.getContext('2d').getImageData(0,0,w,h).data,cols=new Uint32Array(w),rows=new Uint32Array(h);
 for(let y=0;y<h;y++)for(let x=0;x<w;x++){const k=(y*w+x)*4;if(d[k+3]>90&&Math.max(d[k],d[k+1],d[k+2])>130){cols[x]++;rows[y]++;}}
 const cx=Math.max(...cols)*.03,cy=Math.max(...rows)*.03;
 let x=cols.findIndex(v=>v>cx),y=rows.findIndex(v=>v>cy),r=w-1,b=h-1;
 while(r>x&&cols[r]<=cx)r--;while(b>y&&rows[b]<=cy)b--;
 if(x<0||y<0)return crop(canvas);x=Math.max(0,x-8);y=Math.max(0,y-8);
 return {x,y,w:Math.min(w-x,r-x+17),h:Math.min(h-y,b-y+17)};
}
function connectedBodyCrop(canvas){
 const w=canvas.width,h=canvas.height,d=canvas.getContext('2d').getImageData(0,0,w,h).data,seen=new Uint8Array(w*h),queue=new Int32Array(w*h);let best=null;
 for(let seed=0;seed<w*h;seed++){
  if(seen[seed])continue;const k=seed*4;seen[seed]=1;if(d[k+3]<90||Math.max(d[k],d[k+1],d[k+2])<130)continue;
  let head=0,tail=1,x0=seed%w,x1=x0,y0=Math.floor(seed/w),y1=y0;queue[0]=seed;
  while(head<tail){const at=queue[head++],x=at%w,y=Math.floor(at/w);x0=Math.min(x0,x);x1=Math.max(x1,x);y0=Math.min(y0,y);y1=Math.max(y1,y);
   for(let dy=-1;dy<=1;dy++)for(let dx=-1;dx<=1;dx++){if(!dx&&!dy)continue;const xx=x+dx,yy=y+dy;if(xx<0||yy<0||xx>=w||yy>=h)continue;const next=yy*w+xx;if(seen[next])continue;seen[next]=1;const j=next*4;if(d[j+3]>=90&&Math.max(d[j],d[j+1],d[j+2])>=130)queue[tail++]=next;}
  }
  if(!best||tail>best.area)best={area:tail,x0,x1,y0,y1};
 }
 if(!best)return coreCrop(canvas);const x=Math.max(0,best.x0-9),y=Math.max(0,best.y0-9);
 return {x,y,w:Math.min(w-1,best.x1+9)-x+1,h:Math.min(h-1,best.y1+9)-y+1};
}
function outlineProfile(canvas,b){
 const w=canvas.width,h=canvas.height,d=canvas.getContext('2d').getImageData(0,0,w,h).data,left=Array(96).fill(Infinity),right=Array(96).fill(-Infinity);
 for(let y=Math.max(0,Math.floor(b.y));y<Math.min(h,b.y+b.h);y++)for(let x=Math.max(0,Math.floor(b.x));x<Math.min(w,b.x+b.w);x++){const k=(y*w+x)*4;if(d[k+3]>90&&Math.max(d[k],d[k+1],d[k+2])>100){const row=Math.min(95,Math.max(0,Math.floor((y-b.y)/b.h*96))),u=(x-b.x)/b.h;left[row]=Math.min(left[row],u);right[row]=Math.max(right[row],u);}}
 return {left,right};
}
function fungiKerning(a,b){if(!a?.e?.profile||!b?.e?.profile)return 0;let clearance=Infinity;for(let i=0;i<96;i++){const r=a.e.profile.right[i],l=b.e.profile.left[i];if(Number.isFinite(r)&&Number.isFinite(l))clearance=Math.min(clearance,a.w-r+l);}return Number.isFinite(clearance)?Math.min(.28,Math.max(0,clearance-.035)):0;}
function removeFunction(code,name){const marker='function '+name+'()';const start=code.indexOf(marker);if(start<0)return code;const open=code.indexOf('{',start);let end=open+1,depth=1;while(depth&&end<code.length){if(code[end]==='{')depth++;if(code[end]==='}')depth--;end++}return code.slice(0,open+1)+code.slice(end-1);}
// Native field simulations run in a small worker pool, leaving UI and compositing free.
const bacteriaWorkers=[];let bacteriaWorkerEnabled=true,workerSerial=0;const workerRecords=new Map();
function workerEngine(kind,letter,source){return new Promise((resolve,reject)=>{
 const index=workerSerial++%Math.min(3,Math.max(1,(navigator.hardwareConcurrency||4)-1));
 if(!bacteriaWorkers[index]){const worker=new Worker(URL.createObjectURL(new Blob([window.LAB_BACTERIA_WORKER],{type:'text/javascript'})));
  worker.onmessage=({data:m})=>{const record=workerRecords.get(m.id);if(!record){m.bitmap?.close();return}if(m.error){record.reject(Error(m.error));return}record.canvas?.close();record.canvas=m.bitmap;record.bounds=m.bounds;record.quality=m.quality;record.pending=false;if(m.init)record.resolve(record)};
  worker.onerror=event=>{for(const record of workerRecords.values())if(record.worker===worker)record.reject(Error(event.message||'Worker unavailable'));};
  bacteriaWorkers[index]=worker;
 }
 const worker=bacteriaWorkers[index],id=kind+letter+'-'+workerSerial;
 const timeout=setTimeout(()=>{workerRecords.delete(id);reject(Error('Worker startup timed out'))},4000);
 const record={worker,canvas:null,bounds:null,pending:true,resolve:e=>{clearTimeout(timeout);resolve(e)},reject:e=>{clearTimeout(timeout);workerRecords.delete(id);reject(e)},time:0,lastT:0,at(t){if(this.pending)return;this.time+=Math.max(0,Math.min(.15,t-this.lastT));this.lastT=t;this.pending=true;worker.postMessage({type:'frame',id,t:this.time})},dispose(){workerRecords.delete(id);this.canvas?.close();worker.postMessage({type:'dispose',id})}};
 workerRecords.set(id,record);worker.postMessage({type:'init',id,kind,source});
})}
async function makeEngine(kind,letter){
 const source=LAB_SOURCES[kind][letter];if(!source)return null;
 if((kind==='bacteriaB'||kind==='bacteriaC')&&bacteriaWorkerEnabled&&typeof Worker!=='undefined'&&typeof OffscreenCanvas!=='undefined'){try{return await workerEngine(kind,letter,source)}catch(error){bacteriaWorkerEnabled=false;console.info('Using native canvas fallback:',error.message)}};
 if(kind==='fungi'){
  const e=Function('document',source.replace('window.devicePixelRatio=.5;','window.devicePixelRatio=1;').replace('resolution:.5','resolution:1'))(document);e.complete();e.bounds=crop(e.canvas);if(letter==='L'){e.at(5.25);e.bounds=crop(e.canvas);}e.profile=outlineProfile(e.canvas,e.bounds);return e;
 }
 if(kind==='bacteriaA'){
  const box=document.createElement('div');host.append(box);const html=source.html;
  box.innerHTML=html.slice(html.indexOf('<body>')+6,html.lastIndexOf('</body>')).replace(/<script[\s\S]*?<\/script>/g,'');
  const doc={getElementById:id=>box.querySelector('#'+id),querySelector:s=>box.querySelector(s),querySelectorAll:s=>box.querySelectorAll(s),body:box,createElement:tag=>document.createElement(tag),addEventListener(){}};
  let code=[...html.matchAll(/<script(?:\s[^>]*)?>([\s\S]*?)<\/script>/g)].map(m=>m[1]).join('\n');
  code=removeFunction(code,'drawDish');
  code=code.replace(/let stage = 2, stageTarget = 2;/,'let stage = 0, stageTarget = 0;')
   .replace('const TEXTURE_SIZE=560;','const TEXTURE_SIZE=400;')
   .replace('Math.hypot(gradX,gradY)','Math.sqrt(gradX*gradX+gradY*gradY)')
   .replace('          const textureIndex=y*N+x;','          if(distance>9){pixels[k]=pixels[k+1]=pixels[k+2]=255;continue;}\n          const textureIndex=y*N+x;')
   .replace('p.pixelDensity(Math.min(window.devicePixelRatio || 1, 2));','p.pixelDensity(1);')
   .replace('let animationFrame = 0;', 'let animationFrame = 0; p.labStartBold=()=>{animationFrame=FORMATION_HOLD+FORMATION_DURATION+1};')
   .replace('const PLAYBACK_RATE = 1.25;','let PLAYBACK_RATE = 1.25; p.labSetRate=v=>{PLAYBACK_RATE=1.25*v};')
   .replace('        const gradX=', '        if(value<.015){pixels[k]=pixels[k+1]=pixels[k+2]=0;continue;}\n        const gradX=');
  code=code.replace('p.frameRate(30);','p.frameRate(30);p.noLoop();');
  let instance;function Native(sketch){instance=new p5(sketch,box);return instance}
  Function('document','p5',code)(doc,Native);
  for(let i=0;!instance?.canvas&&i<100;i++)await new Promise(r=>setTimeout(r,20));
  if(!instance?.canvas)throw Error('Bacteria engine did not start');
  instance.noLoop();instance.labStartBold?.();const thickness=box.querySelector('#thickness');if(thickness){thickness.value='2';thickness.dispatchEvent(new Event('input'));}
  for(let i=0;i<24;i++){instance.redraw();if(i%5===4)await new Promise(r=>setTimeout(r,0));}
  const bounds=letter==='V'?connectedBodyCrop(instance.canvas):coreCrop(instance.canvas);let previous=0,acc=0;
  return {canvas:instance.canvas,bounds,at(t){acc+=Math.max(0,Math.min(.08,t-previous))*30;previous=t;if(acc>=1){instance.labSetRate?.(Math.min(acc,2.4));instance.redraw();acc=0;}},dispose(){instance.remove();box.remove()}};
 }
 const canvas=document.createElement('canvas');canvas.width=canvas.height=kind==='amoeba'?600:kind==='bacteriaC'?640:900;canvas.getBoundingClientRect=()=>({width:canvas.width});
 const nodes={};for(const [id,v]of Object.entries(source.nodes))nodes[id]={...v,textContent:'',innerHTML:'',matches:()=>false,addEventListener(){}};
 const doc={querySelector:s=>s==='#dish'||s==='#view'||s==='canvas'?canvas:nodes[s.slice(1)]||(nodes[s.slice(1)]={value:'0',checked:false,textContent:''}),getElementById:id=>id==='dish'?canvas:nodes[id]||(nodes[id]={value:'0',checked:false,textContent:''}),querySelectorAll:()=>[],addEventListener(){},createElement:()=>document.createElement('canvas')};
 let code=source.code;
 if(kind==='bacteriaC')code=code.replace('Math.round(10+245*ink)','Math.round(255*ink)');
 if(kind==='protozoa'){
  code=code.replace("ctx.beginPath();ctx.arc(450,450,368,0,TAU);ctx.strokeStyle='#686868';ctx.lineWidth=.8;ctx.stroke();",'');
  code=code.slice(0,code.lastIndexOf('return {canvas,at(t)'))+"document.querySelector('#assembled').onclick();const heldState=state;state=function(){formation='hold';phaseStarted=time-1;const result=heldState();formation='hold';return result;};return {canvas,at(t){let remaining=Math.min(.08,Math.max(0,t-(this.previous||t)));this.previous=t;while(remaining>0){const dt=Math.min(1/60,remaining);time+=dt;state();remaining-=dt}draw()},formed:0,duration:30};";
 }
 const e=Function('document','window','requestAnimationFrame','addEventListener',code)(doc,{devicePixelRatio:1,addEventListener(){}},()=>{},()=>{});
 e.at(e.formed);e.bounds=crop(canvas);return e;
}
const pendingEngines=new Map();let prewarmGeneration=0;
function obtainEngine(kind,letter){
 const key=kind+letter;if(engines.has(key)){const e=engines.get(key);engines.delete(key);engines.set(key,e);return Promise.resolve(e);}
 if(pendingEngines.has(key))return pendingEngines.get(key);
 const job=makeEngine(kind,letter).then(e=>{if(e)engines.set(key,e);return e;}).finally(()=>pendingEngines.delete(key));pendingEngines.set(key,job);return job;
}
function trimEngines(){
 const keep=new Set([...text.replace(/ /g,'')].map(l=>(species==='bacteria'?'bacteria'+bacteriaType:species)+l));
 // Retain a bounded, inactive cache so repeated switches do not rebuild chemistry.
 for(const [key,e]of engines){if(engines.size<=24)break;if(!keep.has(key)){e.dispose?.();engines.delete(key);}}
}
function prewarmBacteria(){
 const token=++prewarmGeneration,letters=[...new Set(text.replace(/ /g,''))];
 setTimeout(async()=>{if(token!==prewarmGeneration||!bacteriaWorkerEnabled||printing)return;
  for(const kind of ['bacteriaB','bacteriaC']){
   if(token!==prewarmGeneration)return;
   await Promise.all(letters.map(l=>obtainEngine(kind,l).catch(()=>null)));trimEngines();
  }
 },500);
}
async function prepare(){
 const id=++generation;++prewarmGeneration;ready=false;document.querySelector('#print').disabled=true;status.textContent='PREPARING / '+species.toUpperCase();
 const kind=species==='bacteria'?'bacteria'+bacteriaType:species,letters=[...new Set(text.replace(/ /g,''))];
 try{
  const list=[];
  if(kind==='bacteriaB'||kind==='bacteriaC'){
   const entries=await Promise.all(letters.map(async letter=>[letter,await obtainEngine(kind,letter)]));list.push(...entries.filter(e=>e[1]));
  }else for(const letter of letters){const e=await obtainEngine(kind,letter);if(id!==generation)return;if(e)list.push([letter,e]);status.textContent='PREPARING / '+species.toUpperCase()+' '+list.length+'/'+letters.length;await new Promise(r=>setTimeout(r,0));}
  if(id!==generation)return;active=new Map(list);if(kind==='amoeba'&&list.length){const ts=list.map(([,e])=>e.timing);amoebaSchedule={grow:ts.reduce((n,t)=>n+t.formed,0)/ts.length,hold:ts.reduce((n,t)=>n+t.hold,0)/ts.length,recover:ts.reduce((n,t)=>n+t.recovery,0)/ts.length};}clock=kind==='fungi'?3:0;last=0;ready=true;document.querySelector('#print').disabled=false;status.textContent='LIVE / '+(species==='bacteria'?'BACTERIA\nTYPE '+bacteriaType:kind.toUpperCase());
  trimEngines();prewarmBacteria();
 }catch(error){status.textContent='ENGINE UNAVAILABLE / '+kind.toUpperCase();console.error(error)}
}
function resize(){if(printing||matchMedia('print').matches)return;const dpr=Math.min(devicePixelRatio||1,2);stage.width=Math.round(innerWidth*dpr);stage.height=Math.round(innerHeight*dpr);stage.style.width=innerWidth+'px';stage.style.height=innerHeight+'px';}
function render(){
 if(!ready)return;
 const W=stage.width,H=stage.height;ctx.globalCompositeOperation='source-over';ctx.fillStyle=ready?'#000':'#0c0e0d';ctx.fillRect(0,0,W,H);if(!ready)return;
 if(species==='amoeba'){
  const tm=amoebaSchedule,total=tm.grow+tm.hold+tm.recover,t=(clock*1.12)%total;
  const grow=Math.min(1,t/tm.grow),hold=Math.max(0,Math.min(1,(t-tm.grow)/tm.hold)),recover=Math.max(0,Math.min(1,(t-tm.grow-tm.hold)/tm.recover));
  for(const e of active.values())e.atPhase(grow,hold,recover);
  window.amoebaPhase={grow,hold,recover,rate:1.12,total};
 }else for(const e of active.values())e.at(species==='fungi'?clock%11.5:clock);
 const items=[...text].map(l=>{const e=active.get(l),b=e?.bounds;
  // A pointed V needs a small optical overshoot; apply uniform scale to
  // preserve its shape. H receives the smaller measured cap-height correction.
  const optical=species==='bacteria'&&bacteriaType==='A'?(l==='V'?1.025:l==='H'?1.02:1):1;
  return {letter:l,e,b,optical,w:b?b.w/b.h*optical:l===' '?.3:.6,reference:e?e.bounds.w/e.bounds.h*optical:l===' '?.3:.6};
 });
 const unit=items.reduce((n,i)=>n+i.w,0),width=innerWidth,height=innerHeight;
 // The native fungi bounds included invisible side bearings. Use the actual
 // mature ink bounds, so spacing is measured from letter edges, not canvases.
 const rail=document.querySelector('aside').getBoundingClientRect();
 const safeW=Math.max(100,width-2*(width-rail.left+28));
 const safeH=Math.max(100,height-2*Math.max(160,height*.18));
 const count=Math.max(0,items.length-1),gapRatio=species==='bacteria'?.002+.08*Math.pow(1-density,2):.006+.22*Math.pow(1-density,2);
 // Keep size constant through the tight part of the slider: it now closes
 // the actual gaps instead of compensating by enlarging each letter.
 const referenceUnit=items.reduce((n,i)=>n+i.reference,0);
 const h=Math.max(10,Math.min(safeH,height*.48,520,safeW/Math.max(.1,referenceUnit+.03*count),safeW/Math.max(.1,unit+gapRatio*count)));
 const gap=Math.max(1.5,h*gapRatio);
 const kern=items.map((a,i)=>species==='fungi'&&a.letter==='L'?fungiKerning(a,items[i+1]):0);
 const total=(unit-kern.reduce((a,b)=>a+b,0))*h+gap*count,ratio=W/width;
 const centerX=width/2-Math.min(100,width*.065);let x=centerX-total/2;
 ctx.save();ctx.globalCompositeOperation='screen';ctx.scale(ratio,ratio);ctx.imageSmoothingEnabled=species!=='protozoa';
 for(const [index,{e,b,w,optical}]of items.entries()){if(e){ctx.drawImage(e.canvas,b.x*(e.resolution||1),b.y*(e.resolution||1),b.w*(e.resolution||1),b.h*(e.resolution||1),x,(height-h*optical)/2,w*h,h*optical)}x+=w*h+gap-kern[index]*h}
 // Tint only rendered material; black source backgrounds stay transparent.
 ctx.restore();ctx.globalCompositeOperation='multiply';ctx.fillStyle=palettes[species];ctx.fillRect(0,0,W,H);ctx.globalCompositeOperation='screen';ctx.fillStyle='#0c0e0d';ctx.fillRect(0,0,W,H);ctx.globalCompositeOperation='source-over';
 window.labLayout={center:{x:centerX,y:height/2},bounds:{x:centerX-total/2,y:(height-h)/2,width:total,height:h},gap,species,bacteriaType:species==='bacteria'?bacteriaType:null,text};
}
function frame(now){requestAnimationFrame(frame);if(document.hidden||printing||matchMedia('print').matches){last=0;return}if(last)clock+=Math.min(.08,(now-last)/1000)*speed;last=now;if(now-paint<(species==='bacteria'?1000/30:50))return;paint=now;render();if(ready&&now-receiptCachedAt>1500){receiptCachedAt=now;prepareReceipt(false)}}
for(const button of document.querySelectorAll('[data-species]'))button.onclick=()=>{if(species===button.dataset.species)return;species=button.dataset.species;document.querySelector('#bacteria-types').hidden=species!=='bacteria';document.documentElement.style.setProperty('--ink',palettes[species]);for(const b of document.querySelectorAll('[data-species]'))b.setAttribute('aria-pressed',String(b===button));prepare()};
for(const button of document.querySelectorAll('[data-bacteria-type]'))button.onclick=()=>{if(bacteriaType===button.dataset.bacteriaType)return;bacteriaType=button.dataset.bacteriaType;for(const b of document.querySelectorAll('[data-bacteria-type]'))b.setAttribute('aria-pressed',String(b===button));prepare()};
document.querySelector('#refresh').onclick=async()=>{
 const kind=species==='bacteria'?'bacteria'+bacteriaType:species;++prewarmGeneration;
 for(const [key,e]of engines)if(key.startsWith(kind)){e.dispose?.();engines.delete(key);}
 await prepare();
};
let timer;document.querySelector('#text').addEventListener('input',e=>{const start=e.target.selectionStart;e.target.value=e.target.value.toUpperCase().replace(/[^A-Z ]/g,'').slice(0,16);e.target.setSelectionRange(start,start);clearTimeout(timer);timer=setTimeout(()=>{text=e.target.value.trim();prepare()},350)});
for(const name of ['speed','density'])document.querySelector('#'+name).oninput=e=>{const v=+e.target.value;document.querySelector('#'+name+'-value').value=v.toFixed(2);if(name==='speed')speed=v;else density=v};
function prepareReceipt(refresh=true){
 if(!ready||!text)return null;if(refresh)render();
 const b=window.labLayout.bounds,scale=stage.width/innerWidth,pad=10;
 const sx=Math.max(0,(b.x-pad)*scale),sy=Math.max(0,(b.y-pad)*scale);
 const sw=Math.min(stage.width-sx,(b.width+pad*2)*scale),sh=Math.min(stage.height-sy,(b.height+pad*2)*scale);
 // 576 dots = 72 mm printable width on a typical 203 dpi receipt printer.
 const paper=document.createElement('canvas');paper.width=576;paper.height=Math.max(1,Math.ceil(Math.min(256,576*sh/sw)));
 const ink=paper.getContext('2d',{willReadFrequently:true});ink.fillStyle='#0c0e0d';ink.fillRect(0,0,paper.width,paper.height);
 const fit=Math.min(paper.width/sw,paper.height/sh),w=sw*fit,h=sh*fit;
 ink.drawImage(stage,sx,sy,sw,sh,(paper.width-w)/2,(paper.height-h)/2,w,h);
 const pixels=ink.getImageData(0,0,paper.width,paper.height);
 for(let i=0;i<pixels.data.length;i+=4){
  const material=Math.max(pixels.data[i],pixels.data[i+1],pixels.data[i+2]);
  const value=Math.round(255*(1-Math.max(0,Math.min(1,(material-16)/150))));
  pixels.data[i]=pixels.data[i+1]=pixels.data[i+2]=value;pixels.data[i+3]=255;
 }
 ink.putImageData(pixels,0,0);
 document.querySelector('#receipt-specimen').textContent=species.toUpperCase()+(species==='bacteria'?' / TYPE '+bacteriaType:'')+' / SPECIMEN RECORD';
 document.querySelector('#receipt-word').textContent=text;
 const img=document.querySelector('#print-image');img.src=paper.toDataURL('image/png');return img;
}
document.querySelector('#print').onclick=async()=>{
 try{
  printing=true;
  const img=prepareReceipt();if(!img){printing=false;return;}
  if(typeof img.decode==='function')await img.decode();
  else if(!img.complete||!img.naturalWidth)await new Promise((resolve,reject)=>{img.onload=resolve;img.onerror=reject});
  // Safari must receive this exact decoded image; beforeprint must not replace it.
  await new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)));
  window.print();
 }catch(error){printing=false;status.textContent='PRINT IMAGE NOT READY / PLEASE RETRY';console.error(error)}
};
// Browser File → Print uses the snapshot already cached during screen rendering.
// Re-rendering or changing img.src here races Safari's print-layout snapshot.
addEventListener('beforeprint',()=>{printing=true});
addEventListener('afterprint',()=>{printing=false;last=0;receiptCachedAt=0;resize()});
addEventListener('resize',resize);resize();prepare();requestAnimationFrame(frame);

// Exhibition shortcut: F toggles fullscreen when the visitor is not typing.
addEventListener('keydown',e=>{if(e.key.toLowerCase()==='f'&&e.target.tagName!=='INPUT'){if(document.fullscreenElement)document.exitFullscreen();else document.documentElement.requestFullscreen?.()}});
