// Symbol referencing the constructor type in javascript Objects
const c = Symbol.for('cons');

// A term is an ADT represented by a JSON
function Typ ()                           { return {[c]:'Typ'   }; }
function Knd ()                           { return {[c]:'Knd'   }; }
function Var (index, preferred_name=null) { return {[c]:'Var' , index, preferred_name}; }
function Ref (name)                       { return {[c]:'Ref' , name}; }
function All (name, dom, cod)             { return {[c]:'All' , name, dom, cod}; }
function Lam (name, type, body)           { return {[c]:'Lam' , name, type, body}; }
function App (func, argm)                 { return {[c]:'App' , func, argm}; }
// Chains applications:  app(a,[b,c,d])  returns  App(App(App(a,b),c),d)
function app(func, args) { return args.reduce(App,func); }

// A pattern is a term extended with (potentially anonymous) meta-variables which are "stars" when "fully" applied
function MVar(name=null,args=[]) { return {[c]:'MVar', name, args}; }
function Star()                  { return {[c]:'Star'}; }

// Returns the head of a term together with the list of its arguments *in reverse order*
function get_head(t) {
  const args = [];
  while (t[c] == 'App') {
    args.push(t.argm);
    t = t.func;
  }
  return [t,args];
}


// Pre-scoping objects that can be either references or locally bounded variables
function PreScope(name) { return {[c]:'PreScope', name}; }
function PreRef(name)   { return {[c]:'PreRef', name}; }

// Instructions 
function Decl(name,params,type)    { return {[c]:'Decl',name,type}; }
function Def(name,params,type,def) { return {[c]:'Def' ,name,type,def}; }
function Rew(lhs,rhs,name)         { return {[c]:'Rew' ,lhs,rhs,name}; }
function CmdReq(module)            { return {[c]:'Req', module}; }
function CmdEval(term)             { return {[c]:'Eval', term}; }
function CmdInfer(term)            { return {[c]:'Infer', term}; }
function CmdCheckType(term,type)   { return {[c]:'CheckType', term, type}; }
function CmdCheckConv(lhs,rhs)     { return {[c]:'CheckConv', lhs, rhs}; }
function CmdPrint(term)            { return {[c]:'Print', term}; }


// Shifts variables deeper than [depth] by [inc] in the term [term]
function shift(term, inc=1, depth=0) {
  switch (term[c]) {
    case "Typ": return Typ();
    case "Star": return Star();
    case "Var":
      return Var(term.index < depth ? term.index : term.index + inc);
    case "Ref":
      return Ref(term.name);
    case "All":
      const dom = shift(term.dom,inc,depth+1);
      const cod = shift(term.cod,inc,depth  );
      return All(term.name,dom,cod);
    case "Lam":
      const type = term.type && shift(term.type, inc, depth  );
      const body =              shift(term.body, inc, depth+1);
      return Lam(term.name, type, body);
    case "App":
      return App(shift(term.func, inc, depth), shift(term.argm, inc, depth));
    case "MVar":
      return MVar(term.name,term.args.map((t)=>shift(t, inc, depth)));
    default:
      throw "Shift:\nUnexpected constructor:"+term[c];
  }
}

// Check that a and b have compatible head. Stacks conversion-relevant subterms in t.
function same_head(a,b,acc) {
  if (a[c] !== b[c]) { return false; }
  switch (a[c]) {
    case "Var":
      if (a.index !== b.index) { return false; }
      break;
    case "Ref":
      if (a.name !== b.name) { return false; }
      break;
    case "All":
      acc.push({a:a.dom,b:b.dom});
      acc.push({a:a.cod,b:b.cod});
      break;
    case "Lam":
      acc.push({a:a.body,b:b.body});
      break;
    case "App":
      acc.push({a:a.func,b:b.func});
      acc.push({a:a.argm,b:b.argm});
      break;
    case "MVar":
      if (a.name !== b.name || a.args.length !== b.args.length) { return false; }
      for (let i = 0; i < a.args.length; i++) {
        acc.push({a:a.args[i],b:b.args[i]});
      }
      break;
    case "Typ":
    case "Knd":
    case "Star": break;
    default: throw "Equals:\nUnexpected constructor: "+term[c];
  }
  return true;
}

function equals(u, v) {
  const acc = [ {a:u,b:v} ];
  while (acc.length > 0) {
    const {a,b} = acc.pop();
    if (a == b) { continue; }
    if (!same_head(a,b,acc)) { return false; }
  }
  return true;
}
