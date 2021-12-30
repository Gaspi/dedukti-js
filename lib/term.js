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
