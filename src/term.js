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

// A pattern is a term extended with (potentially anonymous) meta-variables
// A "joker" is an anonym fully applied meta-variable. A default name and the full list of args are assigned at scoping.
function MVar(name=null,args=[]) { return {[c]:'MVar', name, args, joker:false}; }
function Joker()                 { return {[c]:'MVar', joker:true}; }

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
function Decl(ln,name,params,type,def,dtype) {
  return {[c]:'Decl', ln, name,
      type: type && params.reduceRight((t,[x,ty])=>All(x,ty,t),type),
      def : def ? params.reduceRight((t,[x,ty])=>Lam(x,ty,t), def ) : undefined,
      constant: dtype==="cst",
      theorem : dtype==="thm",
    };
}
function Rew(ln,lhs,rhs,name,check=true) { return {[c]:'Rew'      , ln, lhs,rhs,name,check }; }
function DeclInj(  ln,name)              { return {[c]:'DeclInj'  , ln, name               }; }
function DeclConst(ln,name)              { return {[c]:'DeclConst', ln, name               }; }
function CmdReq(ln,module,alias)         { return {[c]:'Req'      , ln, module, alias      }; }
function CmdEval(ln,ctx,term)            { return {[c]:'Eval'     , ln, ctx,term           }; }
function CmdInfer(ln,ctx,term)           { return {[c]:'Infer'    , ln, ctx,term           }; }
function CmdCheckType(ln,ctx,term,type)  { return {[c]:'CheckType', ln, ctx,term,type      }; }
function CmdCheckConv(ln,ctx,lhs,rhs,cv) { return {[c]:'CheckConv', ln, ctx,lhs,rhs,cv     }; }
function CmdPrint(ln,term)               { return {[c]:'Print'    , ln, term               }; }
function CmdDTree(ln,name)               { return {[c]:'DTree'    , ln, name               }; }
function CmdTime(ln)                     { return {[c]:'Time'     , ln                     }; }


// Shifts variables deeper than [depth] by [inc] in the term [term]
function shift(term, inc=1, depth=0) {
  switch (term[c]) {
    case "Typ": return Typ();
    case "Var":
      return Var(term.index < depth ? term.index : term.index + inc);
    case "Ref":
      return Ref(term.name);
    case "All":
      const dom = shift(term.dom,inc,depth);
      const cod = shift(term.cod,inc,depth+1);
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
      fail("Shift","Unexpected constructor:"+term[c]);
  }
}

// Check that a and b have compatible head. Stacks conversion-relevant subterms in t.
function same_head(a,b,acc) {
  if (a[c] !== b[c]) { return false; }
  switch (a[c]) {
    case "Var": return a.index == b.index;
    case "Ref": return a.name == b.name;
    case "All":
      acc.push([a.dom,b.dom] , [a.cod,b.cod]);
      break;
    case "Lam":
      acc.push([a.body,b.body]);
      break;
    case "App":
      acc.push([a.func,b.func], [a.argm,b.argm]);
      break;
    case "MVar":
      if (a.name !== b.name || a.args.length !== b.args.length) { return false; }
      for (let i = 0; i < a.args.length; i++) {
        acc.push([a.args[i],b.args[i]]);
      }
      break;
    case "Typ":
    case "Knd": break;
    default: fail("Equals","Unexpected constructor: "+term[c]);
  }
  return true;
}

// Check that a and b have compatible head. Stacks conversion-relevant subterms in t.
function same_head_with_depth(a,b,d,acc) {
  if (a[c] !== b[c]) { return false; }
  switch (a[c]) {
    case "Var": return a.index == b.index;
    case "Ref": return a.name == b.name;
    case "All":
      acc.push([a.dom,b.dom,d] , [a.cod,b.cod,d+1]);
      break;
    case "Lam":
      acc.push([a.body,b.body,d+1]);
      break;
    case "App":
      acc.push([a.func,b.func,d], [a.argm,b.argm,d]);
      break;
    case "MVar":
      if (a.name !== b.name || a.args.length !== b.args.length) { return false; }
      for (let i = 0; i < a.args.length; i++) {
        acc.push([a.args[i],b.args[i],d]);
      }
      break;
    case "Typ":
    case "Knd": break;
    default: fail("Equals","Unexpected constructor: "+term[c]);
  }
  return true;
}

function equals(u, v) {
  const acc = [ [u,v] ];
  while (acc.length > 0) {
    const [a,b] = acc.pop();
    if (a == b) { continue; }
    if (!same_head(a,b,acc)) { return false; }
  }
  return true;
}

// Substitutes [val] for variable with DeBruijn index [depth]
// and downshifts all variables referencing beyond that index:
// subst(  y#0 \x.(x#0 y#1 z#2) , v#9 )  :=  v#8 \x.(x#0 v#9 z#1)
function subst(term, val, depth=0) {
  // Shifts memoisation
  const shifts = [val];
  function s(t,d) {
    switch (t[c]) {
      case "Var":
        if (t.index != d) {
          return Var(t.index - (t.index > d ? 1 : 0));
        } else {
          if (!shifts[d]) { shifts[d] = shift(val,inc=d); }
          return shifts[d];
        }
      case "All" : return All(t.name, s(t.dom,d) , s(t.cod,d+1) );
      case "Lam" : return Lam(t.name, t.type && s(t.type,d) , s(t.body,d+1) );
      case "App" : return App( s(t.func,d) , s(t.argm,d) );
      case "MVar": return MVar(t.name, t.args.map((t)=>s(t,d)) );
      default: return t;
    }
  }
  return s(term,depth);
}

////////////////////////////////////////////////////////////////
///////////////////         Meta terms        //////////////////
////////////////////////////////////////////////////////////////

// Meta-variables substitution
// The map is an object whose keys are meta-variable names
// and values are arrays of shifted terms to substitute
function meta_subst(term, args) {
  // Shift memoisation : maps metavar name to multiple shifted values
  const map = new Map();
  args.forEach((v,k)=>map.set(k,[v]));
  function ms(t,d) {
    switch (t[c]) {
      case "MVar":
        const args = t.args.map((t)=>ms(t,d));
        const s = map.get(t.name);
        if (!s) { return MVar(t.name,args); }
        if (!s[d]) { s[d] = shift(s[0],inc=d); }
        return meta_subst(s[d], args);
      case "All" : return All(t.name, ms(t.dom,d) , ms(t.cod,d+1) );
      case "Lam" : return Lam(t.name, t.type && ms(t.type,d) , ms(t.body,d+1) );
      case "App" : return App( ms(t.func,d) , ms(t.argm,d) );
      default: return t;
    }
  }
  return ms(term,0);
}

/** Checks that given [args] are distinct locally bounded variables [a_0, ..., a_n]
    Returns the substitution { a_0 : MVar(0), ... , a_n : MVar(n) }
*/
function get_meta_match(args) {
  const res = {};
  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    if (a[c]!='Var') { fail("MetaMatch","Expected a locally bounded variable, got:"+pp_term(a)); }
    if (res[a.index]) { fail("MetaMatch","Expected distinct variables, got "+pp_term(a)+"twice"); }
    res[a.index] = MVar(i);
  }
  return res;
}

/** Matches all variables in [term] to the corresponding meta variable in [map]
    Variables beyond [depth] are shifted down by [depth], others raise an error.
*/
function meta_match(term, map, depth) {
  function mm(t,d) {
    switch (t[c]) {
      case "Var":
        if (t.index < d || depth == 0) { return t; }
        if (t.index >= d + depth) { return Var(t.index-depth, t.preferred_name); }
        const m = map[t.index -d];
        if (m) { return  m; }
        else { fail('MetaMatchFailed',""); }
      case "All" : return All(t.name, mm(t.dom,d), mm(t.cod,d+1));
      case "Lam" : return Lam(t.name, t.type && mm(t.type,d) , mm(t.body,d+1) );
      case "App" : return App( mm(t.func,d) , mm(t.argm,d) );
      case "MVar": return MVar(t.name, t.args.map( (t)=>mm(t,d) ));
      default: return t;
    }
  }
  return mm(term,0);
}
