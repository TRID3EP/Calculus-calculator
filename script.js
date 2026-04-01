function normalizeImplicit(expr) {
  return expr
    .replace(/⁰/g, '^0')
    .replace(/²/g, '^2')
    .replace(/³/g, '^3')
    .replace(/¹/g, '^1')
    .replace(/⁴/g, '^4')
    .replace(/⁵/g, '^5')
    .replace(/⁶/g, '^6')
    .replace(/⁷/g, '^7')
    .replace(/⁸/g, '^8')
    .replace(/⁹/g, '^9')
    .replace(/×/g, '*')
    .replace(/·/g, '*')
    .replace(/⋅/g, '*')
    .replace(/÷/g, '/')
    .replace(/√([a-zA-Z0-9_(][^+\-*/^)]*)/g, 'sqrt($1)')
    .replace(/(\d)([a-zA-Z])/g, '$1*$2')
    .replace(/(\d)\(/g, '$1*(')
    .replace(/\)\(/g, ')*(')
    .replace(/\)([a-zA-Z])/g, ')*$1');
}

function compileExpr(expr) {
  var compiled = math.compile(normalizeImplicit(expr));
  return function(x) { return compiled.evaluate({ x: x }); };
}
function tryCompile(expr) {
  try { var fn = compileExpr(expr); fn(1); return { fn: fn, error: null }; }
  catch(e) { return { fn: null, error: e.message }; }
}
function numericalDeriv(f) {
  var h = 1e-5;
  return function(x) { return (f(x+h) - f(x-h)) / (2*h); };
}
var SUP = {'0':'⁰','1':'¹','2':'²','3':'³','4':'⁴','5':'⁵','6':'⁶','7':'⁷','8':'⁸','9':'⁹','-':'⁻'};
function toSup(n) {
  return String(n).split('').map(function(c){ return SUP[c]||c; }).join('');
}
function decToFrac(val) {
  if (Number.isInteger(val)) return null;
  for (var d = 2; d <= 12; d++) {
    var num = Math.round(val * d);
    if (Math.abs(num / d - val) < 1e-9) {
      var g = gcd(Math.abs(num), d);
      var rn = num/g, rd = d/g;
      if (rd === 1) return null;
      return (rn < 0 ? '-' : '') + Math.abs(rn) + '/' + rd;
    }
  }
  return null;
}
function gcd(a, b) { return b < 1e-9 ? a : gcd(b, a % b); }

function fmtCoef(val, forceSign) {
  if (Math.abs(val) < 1e-9) return '0';
  var sign = val < 0 ? '−' : (forceSign ? '+' : '');
  var abs = Math.abs(val);
  var frac = decToFrac(abs);
  if (frac) return sign + frac;
  if (Number.isInteger(abs)) return sign + abs;
  return sign + abs;
}

function fmtExp(expStr) {
  expStr = String(expStr).trim();
  if (/^-?\d+$/.test(expStr)) {
    var ei = parseInt(expStr);
    if (ei === 1) return 'x';
    return 'x' + toSup(ei);
  }
  var fm = expStr.match(/^\(?(-?\d+)\/(\d+)\)?$/);
  if (fm) return 'x^(' + fm[1] + '/' + fm[2] + ')';
  return 'x^(' + expStr + ')';
}

function prettify(raw) {
  if (!raw) return raw;
  var s = raw.trim();

  var m;

  s = s.replace(/x\s*\^\s*\((-?\d+)\/(\d+)\)/g, function(_,n,d){ return 'x^('+n+'/'+d+')'; });
  s = s.replace(/x\s*\^\s*(-?\d+)/g, function(_,e){
    var ei = parseInt(e);
    if (ei === 1) return 'x';
    return 'x' + toSup(ei);
  });

  s = s.replace(/(-?\d+\.\d+)\s*\*/g, function(_, num){
    var v = parseFloat(num);
    var frac = decToFrac(v);
    if (frac) return frac + '*';
    return num + '*';
  });
  s = s.replace(/(-?\d+\.\d+)(?!\s*[*/x])/g, function(_, num){
    var v = parseFloat(num);
    var frac = decToFrac(v);
    return frac || num;
  });

  s = s.replace(/\b1\s*\*\s*(x[⁰¹²³⁴⁵⁶⁷⁸⁹⁻]?)/g, '$1');
  s = s.replace(/-1\s*\*\s*(x[⁰¹²³⁴⁵⁶⁷⁸⁹⁻]?)/g, '-$1');
  s = s.replace(/(\d)\s*\*\s*(x)/g, '$1$2');
  s = s.replace(/([\/\d])\s*\*\s*(x)/g, '$1$2');

  s = s.replace(/\blog\b/g, 'ln');
  s = s.replace(/\bexp\((x[^)]*)\)/g, 'eˣ');

  s = s.replace(/\+-/g, '- ').replace(/\+\s*-/g, '- ');
  s = s.replace(/-/g, '−');
  s = s.replace(/\+/g, ' + ');
  s = s.replace(/\s{2,}/g, ' ');
  s = s.replace(/\*/g, '');

  return s.trim();
}

function symbolicDeriv(expr) {
  try {
    var raw = math.simplify(math.derivative(math.parse(normalizeImplicit(expr)),'x')).toString();
    return prettify(raw);
  }
  catch(e) { return null; }
}
function integrateTerm(term) {
  if (/^-?(\d+(?:\.\d+)?)$/.test(term)) {
    var c = parseFloat(term);
    return c + '*x';
  }
  if (term === 'x') return 'x^2/2';
  var xpow = term.match(/^x\^(-?\d+(?:\.\d+)?)$/);
  if (xpow) {
    var n = parseFloat(xpow[1]);
    if (n === -1) return 'ln(abs(x))';
    var np1 = n + 1;
    return (np1 === 1 ? '' : '1/' + np1 + '*') + 'x^' + np1;
  }
  var cxpow = term.match(/^(-?\d+(?:\.\d+)?)\*x(\^(-?\d+(?:\.\d+)?))?$/);
  if (cxpow) {
    var coef = parseFloat(cxpow[1]);
    var exp2 = cxpow[3] !== undefined ? parseFloat(cxpow[3]) : 1;
    if (exp2 === -1) return coef + '*ln(abs(x))';
    var newExp = exp2 + 1;
    var newCoef = Math.round(coef / newExp * 1e8) / 1e8;
    return newCoef + '*x^' + newExp;
  }
  if (term === 'sin(x)') return '-cos(x)';
  if (term === 'cos(x)') return 'sin(x)';
  if (term === 'exp(x)') return 'exp(x)';
  if (term === 'sqrt(x)') return '(2/3)*x^(3/2)';
  if (term === '1/x') return 'ln(abs(x))';
  if (term === 'ln(x)' || term === 'log(x)') return 'x*ln(x)-x';
  var sinCx = term.match(/^sin\(x\/(-?\d+(?:\.\d+)?)\)$/);
  if (sinCx) { var k = parseFloat(sinCx[1]); return (-k) + '*cos(x/' + k + ')'; }
  var cosCx = term.match(/^cos\(x\/(-?\d+(?:\.\d+)?)\)$/);
  if (cosCx) { var k2 = parseFloat(cosCx[1]); return k2 + '*sin(x/' + k2 + ')'; }
  return null;
}
function splitTerms(expr) {
  var terms = [], depth = 0, cur = '', i = 0;
  while (i < expr.length) {
    var ch = expr[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth--;
    if (depth === 0 && (ch === '+' || ch === '-') && i > 0) {
      if (cur) terms.push(cur);
      cur = ch;
    } else { cur += ch; }
    i++;
  }
  if (cur) terms.push(cur);
  return terms;
}
function symbolicAntideriv(expr) {
  var e = normalizeImplicit(expr.trim()).replace(/\s+/g,'');
  var terms = splitTerms(e);
  var parts = [];
  for (var i = 0; i < terms.length; i++) {
    var t = terms[i].replace(/^\+/, '');
    var result = integrateTerm(t);
    if (result === null) return null;
    parts.push(result);
  }
  var raw = parts.join(' + ').replace(/\+\s*-/g, '- ');
  return prettify(raw) + ' + C';
}
function makeAntideriv(f) {
  return function(x) {
    if (x <= 0) return 0;
    var steps=600, dx=x/steps, sum=0, prev=0;
    try { prev=f(0); } catch(e){}
    for (var i=1;i<=steps;i++){
      var t=i*dx, y=0; try{y=f(t);}catch(e){}
      if(!isFinite(y)) y=prev;
      sum+=(prev+y)/2*dx; prev=y;
    }
    return sum;
  };
}

function makePannable(canvas, view, onUpdate) {
  var dragging=false, lastX=0, lastY=0;
  function getPos(e) {
    var r=canvas.getBoundingClientRect();
    return { px:(e.clientX-r.left)*canvas.width/r.width,
             py:(e.clientY-r.top)*canvas.height/r.height };
  }
  function getTouchPos(e) {
    var r=canvas.getBoundingClientRect();
    return { px:(e.touches[0].clientX-r.left)*canvas.width/r.width,
             py:(e.touches[0].clientY-r.top)*canvas.height/r.height };
  }
  function startDrag(px,py){ dragging=true; lastX=px; lastY=py; canvas.style.cursor='grabbing'; }
  function moveDrag(px,py){
    if(!dragging) return;
    var W=canvas.width, H=canvas.height, PAD=44;
    var xRange=view.xMax-view.xMin, yRange=view.yMax-view.yMin;
    view.xMin -= (px-lastX)/(W-2*PAD)*xRange;
    view.xMax -= (px-lastX)/(W-2*PAD)*xRange;
    view.yMin += (py-lastY)/(H-2*PAD)*yRange;
    view.yMax += (py-lastY)/(H-2*PAD)*yRange;
    lastX=px; lastY=py; onUpdate();
  }
  function endDrag(){ dragging=false; canvas.style.cursor='grab'; }
  canvas.style.cursor='grab';
  canvas.addEventListener('mousedown',function(e){ var p=getPos(e); startDrag(p.px,p.py); });
  window.addEventListener('mousemove',function(e){ if(dragging){ var p=getPos(e); moveDrag(p.px,p.py); }});
  window.addEventListener('mouseup',endDrag);
  canvas.addEventListener('touchstart',function(e){ if(e.touches.length===1){ var p=getTouchPos(e); startDrag(p.px,p.py); }},{passive:true});
  canvas.addEventListener('touchmove',function(e){ if(e.touches.length===1){ e.preventDefault(); var p=getTouchPos(e); moveDrag(p.px,p.py); }},{passive:false});
  canvas.addEventListener('touchend',endDrag);
  canvas.addEventListener('wheel',function(e){
    e.preventDefault();
    var r=canvas.getBoundingClientRect(), PAD=44, W=canvas.width, H=canvas.height;
    var mx=(e.clientX-r.left)*W/r.width, my=(e.clientY-r.top)*H/r.height;
    var wx=view.xMin+(mx-PAD)/(W-2*PAD)*(view.xMax-view.xMin);
    var wy=view.yMin+(H-PAD-my)/(H-2*PAD)*(view.yMax-view.yMin);
    var factor=e.deltaY>0?1.15:0.87;
    view.xMin=wx+(view.xMin-wx)*factor; view.xMax=wx+(view.xMax-wx)*factor;
    view.yMin=wy+(view.yMin-wy)*factor; view.yMax=wy+(view.yMax-wy)*factor;
    onUpdate();
  },{passive:false});
}

function setupCanvas(ctx, W, H, v) {
  var PAD=44;
  ctx.clearRect(0,0,W,H);
  ctx.fillStyle='#0d0d14'; ctx.fillRect(0,0,W,H);
  var toX=function(x){ return PAD+(x-v.xMin)/(v.xMax-v.xMin)*(W-2*PAD); };
  var toY=function(y){ return H-PAD-(y-v.yMin)/(v.yMax-v.yMin)*(H-2*PAD); };
  function niceStep(range, target) {
    var rough=range/target, mag=Math.pow(10,Math.floor(Math.log10(rough)));
    var norm=rough/mag;
    if(norm<1.5) return mag; if(norm<3.5) return 2*mag; if(norm<7.5) return 5*mag; return 10*mag;
  }
  var xs=niceStep(v.xMax-v.xMin,8), ys=niceStep(v.yMax-v.yMin,6);
  ctx.strokeStyle='#1e1e2e'; ctx.lineWidth=1;
  for(var gx=Math.ceil(v.xMin/xs)*xs; gx<=v.xMax+xs*0.01; gx+=xs){
    ctx.beginPath(); ctx.moveTo(toX(gx),0); ctx.lineTo(toX(gx),H); ctx.stroke();
  }
  for(var gy=Math.ceil(v.yMin/ys)*ys; gy<=v.yMax+ys*0.01; gy+=ys){
    ctx.beginPath(); ctx.moveTo(PAD,toY(gy)); ctx.lineTo(W-PAD,toY(gy)); ctx.stroke();
  }
  ctx.strokeStyle='#3a3a5a'; ctx.lineWidth=1.5;
  if(v.yMin<=0&&v.yMax>=0){ ctx.beginPath(); ctx.moveTo(PAD,toY(0)); ctx.lineTo(W-PAD,toY(0)); ctx.stroke(); }
  if(v.xMin<=0&&v.xMax>=0){ ctx.beginPath(); ctx.moveTo(toX(0),0); ctx.lineTo(toX(0),H); ctx.stroke(); }
  ctx.fillStyle='#50507a'; ctx.font='10px JetBrains Mono, monospace';
  var axY=v.yMin<=0&&v.yMax>=0?toY(0):H-PAD/2;
  var axX=v.xMin<=0&&v.xMax>=0?toX(0):PAD;
  ctx.textAlign='center';
  for(var lx=Math.ceil(v.xMin/xs)*xs; lx<=v.xMax+xs*0.01; lx+=xs){
    var lv=parseFloat(lx.toPrecision(6));
    if(Math.abs(lv)<xs*0.01) continue;
    ctx.fillText(lv, toX(lx), Math.min(H-4,axY+14));
  }
  ctx.textAlign='right';
  for(var ly=Math.ceil(v.yMin/ys)*ys; ly<=v.yMax+ys*0.01; ly+=ys){
    var lvy=parseFloat(ly.toPrecision(6));
    if(Math.abs(lvy)<ys*0.01) continue;
    var cy=toY(ly); if(cy>4&&cy<H-4) ctx.fillText(lvy, Math.max(PAD-2,axX-4), cy+3);
  }
  return {toX:toX, toY:toY, PAD:PAD};
}

function plotCurve(ctx,f,W,v,toX,toY,color,lw,shadow) {
  var PAD=44;
  ctx.beginPath(); ctx.strokeStyle=color; ctx.lineWidth=lw||2;
  if(shadow){ctx.shadowColor=shadow; ctx.shadowBlur=10;}
  var first=true;
  for(var px=PAD; px<=W-PAD; px++){
    var x=v.xMin+(px-PAD)/(W-2*PAD)*(v.xMax-v.xMin);
    var y; try{y=f(x);}catch(e){first=true;continue;}
    if(!isFinite(y)||y<v.yMin-2||y>v.yMax+2){first=true;continue;}
    if(first){ctx.moveTo(px,toY(y));first=false;}else{ctx.lineTo(px,toY(y));}
  }
  ctx.stroke(); ctx.shadowBlur=0;
}

(function(){
  var fCanvas=document.getElementById('diffCanvas');
  var oCanvas=document.getElementById('diffOutCanvas');
  var W=680, FH=260, OH=180;
  fCanvas.width=W; fCanvas.height=FH;
  oCanvas.width=W; oCanvas.height=OH;
  var fCtx=fCanvas.getContext('2d');
  var oCtx=oCanvas.getContext('2d');

  var fView={xMin:-4,xMax:4,yMin:-2.5,yMax:2.5};
  var oView={xMin:-4,xMax:4,yMin:-3,yMax:3};

  var currentFn=function(x){return Math.sin(x);};
  var currentDf=numericalDeriv(currentFn);
  var currentExpr='sin(x)';
  var xPos=0, dx=0.5;

  function render(){
    var f=currentFn, df=currentDf;

    var fc=setupCanvas(fCtx,W,FH,fView);
    var toFX=fc.toX, toFY=fc.toY;

    plotCurve(fCtx,f,W,fView,toFX,toFY,'rgba(255,255,255,0.88)',2.5,'rgba(255,255,255,0.2)');

    var x=xPos, y=f(x), x2=x+dx, y2=f(x2);
    var secSlope=(y2-y)/(x2-x), slope=df(x);

    fCtx.beginPath(); fCtx.strokeStyle='rgba(240,165,0,0.5)'; fCtx.lineWidth=1.5;
    fCtx.setLineDash([6,4]);
    fCtx.moveTo(toFX(fView.xMin),toFY(y+secSlope*(fView.xMin-x)));
    fCtx.lineTo(toFX(fView.xMax),toFY(y+secSlope*(fView.xMax-x)));
    fCtx.stroke(); fCtx.setLineDash([]);

    fCtx.beginPath(); fCtx.strokeStyle='#08f903'; fCtx.lineWidth=2;
    fCtx.shadowColor='#ff6b6b'; fCtx.shadowBlur=10;
    fCtx.moveTo(toFX(fView.xMin),toFY(y+slope*(fView.xMin-x)));
    fCtx.lineTo(toFX(fView.xMax),toFY(y+slope*(fView.xMax-x)));
    fCtx.stroke(); fCtx.shadowBlur=0;

    fCtx.beginPath(); fCtx.strokeStyle='rgba(240,165,0,0.35)'; fCtx.lineWidth=1;
    fCtx.setLineDash([3,3]);
    fCtx.moveTo(toFX(x),toFY(y)); fCtx.lineTo(toFX(x2),toFY(y)); fCtx.lineTo(toFX(x2),toFY(y2));
    fCtx.stroke(); fCtx.setLineDash([]);

    fCtx.beginPath(); fCtx.arc(toFX(x2),toFY(y2),4.5,0,2*Math.PI);
    fCtx.fillStyle='rgba(240,165,0,0.6)'; fCtx.fill();

    fCtx.beginPath(); fCtx.arc(toFX(x),toFY(y),6.5,0,2*Math.PI);
    fCtx.fillStyle='#f0a500'; fCtx.shadowColor='#f0a500'; fCtx.shadowBlur=14;
    fCtx.fill(); fCtx.shadowBlur=0;

    fCtx.fillStyle='#ff6b6b'; fCtx.font='bold 11px JetBrains Mono, monospace'; fCtx.textAlign='left';
    fCtx.fillText("f\u2032("+x.toFixed(2)+") = "+slope.toFixed(3), toFX(x)+(x>fView.xMax-1?-160:12), toFY(y)-10);

    var oc=setupCanvas(oCtx,W,OH,oView);
    var toOX=oc.toX, toOY=oc.toY;

    oCtx.beginPath(); oCtx.moveTo(toOX(oView.xMin),toOY(0));
    for(var px=44;px<=W-44;px++){
      var xi=oView.xMin+(px-44)/(W-88)*(oView.xMax-oView.xMin);
      try{var v2=df(xi); if(isFinite(v2)) oCtx.lineTo(px,toOY(v2));}catch(e){}
    }
    oCtx.lineTo(toOX(oView.xMax),toOY(0)); oCtx.closePath();
    var g1=oCtx.createLinearGradient(0,0,0,OH);
    g1.addColorStop(0,'rgba(167,139,250,0.18)'); g1.addColorStop(1,'rgba(167,139,250,0.02)');
    oCtx.fillStyle=g1; oCtx.fill();

    plotCurve(oCtx,df,W,oView,toOX,toOY,'#4408f8',2.5,'#a78bfa');

    var dfv=df(xPos);
    if(isFinite(dfv)&&dfv>=oView.yMin&&dfv<=oView.yMax){
      oCtx.beginPath(); oCtx.arc(toOX(xPos),toOY(dfv),6,0,2*Math.PI);
      oCtx.fillStyle='#f0a500'; oCtx.shadowColor='#f0a500'; oCtx.shadowBlur=14;
      oCtx.fill(); oCtx.shadowBlur=0;
      oCtx.fillStyle='#a78bfa'; oCtx.font='bold 10px JetBrains Mono, monospace';
      oCtx.textAlign=toOX(xPos)>W/2?'right':'left';
      oCtx.fillText("f\u2032("+xPos.toFixed(2)+") = "+dfv.toFixed(3),
        toOX(xPos)+(toOX(xPos)>W/2?-9:9), toOY(dfv)-8);
    }

    oCtx.fillStyle='rgba(167,139,250,0.96)'; oCtx.font='10px JetBrains Mono, monospace';
    oCtx.textAlign='right';
    oCtx.fillText("f\u2032(x) - drag to pan · scroll to zoom", W-44-4, 18);

    var sym=symbolicDeriv(currentExpr);
    document.getElementById('diffExprOut').textContent=sym?"f\u2032(x) = "+sym:"f\u2032(x) = (numerical)";
    document.getElementById('slopeDisplay').textContent=slope.toFixed(4);
    document.getElementById('xVal').textContent=xPos.toFixed(2);
    document.getElementById('dxVal').textContent=dx.toFixed(2);
  }

  makePannable(fCanvas, fView, render);
  makePannable(oCanvas, oView, render);

  function setExpr(expr,inputEl,errorEl){
    var normalized=normalizeImplicit(expr);
    var r=tryCompile(normalized); if(r.error){inputEl.className='fn-input error';errorEl.textContent='\u26a0 '+r.error.split('\n')[0].slice(0,60);return;}
    currentFn=r.fn; currentDf=numericalDeriv(r.fn); currentExpr=normalized;
    inputEl.className='fn-input ok'; errorEl.textContent='';
    document.querySelectorAll('#diffFuncBtns .func-btn').forEach(function(b){b.classList.remove('active');});
    render();
  }

  var diffInput=document.getElementById('diffFnInput');
  var diffError=document.getElementById('diffFnError');
  document.getElementById('diffFnGo').addEventListener('click',function(){setExpr(diffInput.value.trim(),diffInput,diffError);});
  diffInput.addEventListener('keydown',function(e){if(e.key==='Enter')setExpr(diffInput.value.trim(),diffInput,diffError);});

  document.querySelectorAll('#diffFuncBtns .func-btn').forEach(function(btn){
    btn.addEventListener('click',function(){
      document.querySelectorAll('#diffFuncBtns .func-btn').forEach(function(b){b.classList.remove('active');});
      btn.classList.add('active');
      var expr=btn.dataset.expr;
      diffInput.value=expr; diffInput.className='fn-input'; diffError.textContent='';
      var r=tryCompile(expr);
      if(r.fn){currentFn=r.fn;currentDf=numericalDeriv(r.fn);currentExpr=expr;render();}
    });
  });

  document.getElementById('xSlider').addEventListener('input',function(e){xPos=parseFloat(e.target.value);render();});
  document.getElementById('dxSlider').addEventListener('input',function(e){dx=parseFloat(e.target.value);render();});

  render();
})();

(function(){
  var fCanvas=document.getElementById('intCanvas');
  var oCanvas=document.getElementById('intOutCanvas');
  var W=680, FH=300, OH=180;
  fCanvas.width=W; fCanvas.height=FH;
  oCanvas.width=W; oCanvas.height=OH;
  var fCtx=fCanvas.getContext('2d');
  var oCtx=oCanvas.getContext('2d');

  var fView={xMin:-0.5,xMax:5.5,yMin:-0.3,yMax:2.4};
  var oView={xMin:-0.5,xMax:5.5,yMin:-0.5,yMax:4};

  var currentFn=function(x){return Math.sin(x)+1;};
  var currentExpr='sin(x)+1';
  var n=8, b=3, a=0;

  function render(){
    var f=currentFn;

    var fc=setupCanvas(fCtx,W,FH,fView);
    var toX=fc.toX, toY=fc.toY;

    var step=(b-a)/n, rSum=0;
    for(var i=0;i<n;i++){
      var xi=a+i*step, fv; try{fv=f(xi+step/2);}catch(e){continue;}
      if(!isFinite(fv))continue;
      fv=Math.max(0,fv); rSum+=fv*step;
      var rx=toX(xi), rw=toX(xi+step)-toX(xi), ry=toY(fv), rh=toY(0)-ry;
      fCtx.fillStyle='rgba(78,205,196,0.16)'; fCtx.fillRect(rx,ry,rw,rh);
      fCtx.strokeStyle='rgba(78,205,196,0.5)'; fCtx.lineWidth=0.8; fCtx.strokeRect(rx,ry,rw,rh);
    }

    fCtx.beginPath(); fCtx.moveTo(toX(a),toY(0));
    for(var px=Math.max(44,toX(a));px<=Math.min(W-44,toX(b));px++){
      var xi2=fView.xMin+(px-44)/(W-88)*(fView.xMax-fView.xMin);
      var y2; try{y2=f(xi2);}catch(e){continue;}
      if(!isFinite(y2))continue; fCtx.lineTo(px,toY(y2));
    }
    fCtx.lineTo(toX(b),toY(0)); fCtx.closePath();
    var g2=fCtx.createLinearGradient(0,0,0,FH);
    g2.addColorStop(0,'rgba(78,205,196,0.13)'); g2.addColorStop(1,'rgba(78,205,196,0.02)');
    fCtx.fillStyle=g2; fCtx.fill();

    plotCurve(fCtx,f,W,fView,toX,toY,'rgba(255,255,255,0.88)',2.5,'rgba(255,255,255,0.2)');

    var fa=0,fb=0; try{fa=f(a);}catch(e){} try{fb=f(b);}catch(e){}
    fCtx.strokeStyle='rgba(240,165,0,0.6)'; fCtx.lineWidth=1.5; fCtx.setLineDash([4,3]);
    fCtx.beginPath(); fCtx.moveTo(toX(a),toY(0)); fCtx.lineTo(toX(a),toY(Math.max(0,fa))); fCtx.stroke();
    fCtx.beginPath(); fCtx.moveTo(toX(b),toY(0)); fCtx.lineTo(toX(b),toY(Math.max(0,fb))); fCtx.stroke();
    fCtx.setLineDash([]);
    fCtx.fillStyle='rgba(240,165,0,0.8)'; fCtx.font='11px JetBrains Mono, monospace'; fCtx.textAlign='center';
    fCtx.fillText('a=0',toX(a),toY(0)+16);
    fCtx.fillText('b='+b.toFixed(1),toX(b),toY(0)+16);

    var steps2=5000, dstep=(b-a)/steps2, exact=0;
    for(var j=0;j<steps2;j++){
      var vv; try{vv=f(a+j*dstep+dstep/2);}catch(e){continue;}
      if(isFinite(vv)) exact+=Math.max(0,vv)*dstep;
    }

    fCtx.fillStyle='rgba(78,205,196,0.85)'; fCtx.font='bold 11px JetBrains Mono, monospace'; fCtx.textAlign='left';
    fCtx.fillText('Riemann \u2248 '+rSum.toFixed(3), 44+8, 44+16);
    fCtx.fillStyle='rgba(255,255,255,0.4)'; fCtx.font='10px JetBrains Mono, monospace';
    fCtx.fillText('error: '+(exact===0?0:Math.abs((rSum-exact)/exact*100).toFixed(2))+'%', 44+8, 44+30);
    document.getElementById('areaDisplay').textContent=exact.toFixed(4);
    document.getElementById('nVal').textContent=n;
    document.getElementById('bVal').textContent=b.toFixed(2);

    var F=makeAntideriv(f);
    var oSteps=W-88;
    var Fvals=[];
    for(var k=0;k<=oSteps;k++){
      var xk=oView.xMin+k/oSteps*(oView.xMax-oView.xMin);
      Fvals.push(xk<0?null:F(xk));
    }
    var validF=Fvals.filter(function(v){return v!==null&&isFinite(v);});
    if(validF.length){
    }

    var oc=setupCanvas(oCtx,W,OH,oView);
    var toOX=oc.toX, toOY=oc.toY;

    oCtx.beginPath(); oCtx.moveTo(toOX(Math.max(0,oView.xMin)),toOY(0));
    for(var k2=0;k2<=oSteps;k2++){
      var xk2=oView.xMin+k2/oSteps*(oView.xMax-oView.xMin);
      if(xk2<0||Fvals[k2]===null)continue;
      oCtx.lineTo(44+k2,toOY(Fvals[k2]));
    }
    oCtx.lineTo(toOX(oView.xMax),toOY(0)); oCtx.closePath();
    var g3=oCtx.createLinearGradient(0,0,0,OH);
    g3.addColorStop(0,'rgba(249,168,212,0.18)'); g3.addColorStop(1,'rgba(249,168,212,0.03)');
    oCtx.fillStyle=g3; oCtx.fill();

    oCtx.beginPath(); oCtx.strokeStyle='#0404f7'; oCtx.lineWidth=2.5;
    oCtx.shadowColor='#f9a8d4'; oCtx.shadowBlur=8;
    var first=true;
    for(var k3=0;k3<=oSteps;k3++){
      var xk3=oView.xMin+k3/oSteps*(oView.xMax-oView.xMin);
      if(xk3<0||Fvals[k3]===null||!isFinite(Fvals[k3])){first=true;continue;}
      var py=toOY(Fvals[k3]); if(py<-10||py>OH+10){first=true;continue;}
      if(first){oCtx.moveTo(44+k3,py);first=false;}else{oCtx.lineTo(44+k3,py);}
    }
    oCtx.stroke(); oCtx.shadowBlur=0;

    var Fb=F(b);
    if(isFinite(Fb)&&Fb>=oView.yMin&&Fb<=oView.yMax){
      oCtx.beginPath(); oCtx.arc(toOX(b),toOY(Fb),6,0,2*Math.PI);
      oCtx.fillStyle='#f0a500'; oCtx.shadowColor='#f0a500'; oCtx.shadowBlur=14;
      oCtx.fill(); oCtx.shadowBlur=0;
      oCtx.fillStyle='#f9a8d4'; oCtx.font='bold 10px JetBrains Mono, monospace';
      oCtx.textAlign=toOX(b)>W/2?'right':'left';
      oCtx.fillText('F('+b.toFixed(1)+') = '+Fb.toFixed(3), toOX(b)+(toOX(b)>W/2?-9:9), toOY(Fb)-8);
    }

    oCtx.fillStyle='rgba(249,168,212,0.6)'; oCtx.font='10px JetBrains Mono, monospace';
    oCtx.textAlign='right';
    oCtx.fillText('F(x) - drag to pan \u00b7 scroll to zoom', W-44-4, 18);

    var sym=symbolicAntideriv(currentExpr);
    document.getElementById('intExprOut').textContent=sym?'F(x) = '+sym:'F(x) = \u222bf(x)dx + C  (numerical)';
  }

  makePannable(fCanvas, fView, render);
  makePannable(oCanvas, oView, render);

  function setExpr(expr,inputEl,errorEl){
    var normalized=normalizeImplicit(expr);
    var r=tryCompile(normalized); if(r.error){inputEl.className='fn-input error';errorEl.textContent='\u26a0 '+r.error.split('\n')[0].slice(0,60);return;}
    currentFn=r.fn; currentExpr=normalized;
    inputEl.className='fn-input ok'; errorEl.textContent='';
    document.querySelectorAll('#intFuncBtns .func-btn').forEach(function(b){b.classList.remove('active');});
    render();
  }

  var intInput=document.getElementById('intFnInput');
  var intError=document.getElementById('intFnError');
  document.getElementById('intFnGo').addEventListener('click',function(){setExpr(intInput.value.trim(),intInput,intError);});
  intInput.addEventListener('keydown',function(e){if(e.key==='Enter')setExpr(intInput.value.trim(),intInput,intError);});

  document.querySelectorAll('#intFuncBtns .func-btn').forEach(function(btn){
    btn.addEventListener('click',function(){
      document.querySelectorAll('#intFuncBtns .func-btn').forEach(function(b){b.classList.remove('active');});
      btn.classList.add('active');
      var expr=btn.dataset.expr;
      intInput.value=expr; intInput.className='fn-input'; intError.textContent='';
      var r=tryCompile(expr);
      if(r.fn){currentFn=r.fn;currentExpr=expr;render();}
    });
  });

  document.getElementById('nSlider').addEventListener('input',function(e){n=parseInt(e.target.value);render();});
  document.getElementById('bSlider').addEventListener('input',function(e){b=parseFloat(e.target.value);render();});

  render();
})();

document.querySelectorAll('.tab').forEach(function(tab){
  tab.addEventListener('click',function(){
    document.querySelectorAll('.tab').forEach(function(t){t.classList.remove('active');});
    document.querySelectorAll('.section').forEach(function(s){s.classList.remove('active');});
    tab.classList.add('active');
    document.getElementById(tab.dataset.tab).classList.add('active');
  });
});