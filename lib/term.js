// Symbol referencing the constructor type in javascript Objects
const c = Symbol.for('cons');

// A term is an ADT represented by a JSON
function Typ ()                           { return {[c]:'Typ'   }; }
function Var (index, preferred_name=null) { return {[c]:'Var' , index, preferred_name}; }
function Ref (name)                       { return {[c]:'Ref' , name}; }
function All (name, dom, cod)             { return {[c]:'All' , name, dom, cod}; }
function Lam (name, type, body)           { return {[c]:'Lam' , name, type, body}; }
function App (func, argm)                 { return {[c]:'App' , func, argm}; }
// A pattern is a term extended with (potentially anonymous) meta-variables which are "stars" when "fully" applied
function MVar(name=null,args)             { return {[c]:'MVar', name, args}; }
function Star()                           { return {[c]:'Star'}; }

function app(func, args) { return args.reduce(App,func); }

// Pre-scoping objects that can be either references or locally bounded variables
function PreScope(name) { return {[c]:'PreScope', name}; }

// Instructions 
function Decl(name,params,type)      { return {[c]:'Decl',name,type}; }
function Def(name,params,type,def)   { return {[c]:'Def' ,name,type,def}; }
function Rew(lhs,rhs,name=undefined) { return {[c]:'Rew' ,lhs,rhs,name}; }
function CmdReq(module)      { return {[c]:'Req', module}; }
function CmdEval(term)       { return {[c]:'Eval', term}; }
function CmdInfer(term)      { return {[c]:'Infer', term}; }
function CmdCheck(term,type) { return {[c]:'Check', term,type}; }
function CmdPrint(term)      { return {[c]:'Print', term}; }

// A context is an array of (name, type, term) triples
function Ctx() { return null; }
function extend(ctx, bind) { return {head: bind, tail: ctx}; }

function Env() { return new Map(); }

function get(env, qualname, must_exist=true) {
  let venv = env;
  const quals = qualname.split('.');
  for (const i = 0; i < quals.length-1; i++) {
    if (!venv[quals[i]]) {
      if (must_exist) {
        throw "[ERROR]\nUndefined reference: `" + qualname + "`.";
      } else {
        venv[quals[i]] = new Env();
      }
    }
    venv = venv[quals[i]];
  }
  let name = quals[quals.length-1]
  if (!venv[name]) {
    if (must_exist) {
      throw "[ERROR]\nUndefined reference: `" + qualname + "`.";
    } else {
      env[name] = Decl(name);
    }
  }
  return env[name];
}