// A term is an ADT represented by a JSON
function Typ ()                           { return {c:'Typ'   }; }
function Knd ()                           { return {c:'Knd'   }; }
function Var (index, preferred_name=null) { return {c:'Var' , index, preferred_name}; }
function Ref (name)                       { return {c:'Ref' , name}; }
function All (name, dom, cod)             { return {c:'All' , name, dom, cod}; }
function Lam (name, type, body)           { return {c:'Lam' , name, type, body}; }
function App (func, argm)                 { return {c:'App' , func, argm}; }
// Chains applications:  app(a,[b,c,d])  returns  App(App(App(a,b),c),d)
function app(func, args) { return args.reduce(App,func); }

// A pattern is a term extended with (potentially anonymous) meta-variables
// A "joker" is an anonym fully applied meta-variable. A default name and the full list of args are assigned at scoping.
function MVar(name=null,args=[]) { return {c:'MVar', name, args, joker:false}; }
function Joker()                 { return {c:'MVar', joker:true}; }

// Returns the head of a term together with the list of its arguments *in reverse order*
function get_head(t) {
  const args = [];
  while (t.c == 'App') {
    args.push(t.argm);
    t = t.func;
  }
  return [t,args];
}

/** Conversion to state representation: [head,stack,subst,meta_subst]
 *  A state [ t, [s2,s1,s0], [s3,s4], {X:s5}, d]
 * represents the term:
 *   t{ X=(tos s5) }{_[0] = (tos s3), _[1]=(tos s4)} (tos s0) (tos s1) (tos s2)
 * TODO: should subst and meta_subst commute ? Should only one be non-empty ?
 * Should one be only extended if the other is empty ? Should one be extended by a substituted version ?
 */
function to_state(term) {
  return [term,[],[],new Map(), 0];
  /* //TODO:deleteme
  return get_head(term).concat([ [], {} ]);
  //*/
}

/** Conversion to/from state representation: [head,stack,subst,meta_subst]
 *  A state [ t, [s2,s1,s0], [s3,s4], {X:s5} ]
 * represents the term:
 *   t{_[0] = (tos s3), _[1]=(tos s4)}{ X=(tos s5) } (tos s0) (tos s1) (tos s2)
 * TODO: should subst and meta_subst commute ? Should only one be non-empty ?
 * Should one be only extended if the other is empty ? Should one be extended by a substituted version ?
 */
function from_state([head, stack, subst, meta_subst, depth]) {
  // Compute the substitution
  let t = head;
  if (meta_subst.length) {
    t = meta_subst(t, meta_subst, 0, from_state);
  }
  if (subst.length) {
    t = subst_l(t, subst, 0, from_state);
  }
  
  // TODO: Finish work
  return stack.map(from_state).reduceRight(App, shift(t,depth) );
}


// Pre-scoping objects that can be either references or locally bounded variables
function PreScope(name) { return {c:'PreScope', name}; }
function PreRef(name)   { return {c:'PreRef', name}; }

// Instructions
function Decl(ln,name,params,type,def,dtype) {
  return {c:'Decl', ln, name,
      type: type && params.reduceRight((t,[x,ty])=>All(x,ty,t),type),
      def : def ? params.reduceRight((t,[x,ty])=>Lam(x,ty,t), def ) : undefined,
      constant: dtype==="cst",
      theorem : dtype==="thm",
    };
}
function Rew(ln,lhs,rhs,name,check=true) { return {c:'Rew'      , ln, lhs,rhs,name,check }; }
function DeclInj(  ln,name)              { return {c:'DeclInj'  , ln, name               }; }
function DeclConst(ln,name)              { return {c:'DeclConst', ln, name               }; }
function CmdReq(ln,module,alias)         { return {c:'Req'      , ln, module, alias      }; }
function CmdEval(ln,ctx,term)            { return {c:'Eval'     , ln, ctx,term           }; }
function CmdInfer(ln,ctx,term)           { return {c:'Infer'    , ln, ctx,term           }; }
function CmdCheckType(ln,ctx,term,type)  { return {c:'CheckType', ln, ctx,term,type      }; }
function CmdCheckConv(ln,ctx,lhs,rhs,cv) { return {c:'CheckConv', ln, ctx,lhs,rhs,cv     }; }
function CmdPrint(ln,term)               { return {c:'Print'    , ln, term               }; }
function CmdDTree(ln,name)               { return {c:'DTree'    , ln, name               }; }
function CmdTime(ln)                     { return {c:'Time'     , ln                     }; }
function CmdDebugOn(ln)                  { return {c:'DebugOn'  , ln                     }; }
function CmdDebugOff(ln)                 { return {c:'DebugOff' , ln                     }; }


// Shifts variables deeper than [depth] by [inc] in the term [term]
function shift(term, inc=1, depth=0) {
  switch (term.c) {
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
      fail("Shift","Unexpected constructor:"+term.c);
  }
}

// Check that a and b have compatible head. Stacks conversion-relevant subterms in t.
function same_head(a,b,acc) {
  if (a.c !== b.c) { return false; }
  switch (a.c) {
    case "Var": return a.index === b.index;
    case "Ref": return a.name === b.name;
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
    default: fail("Equals","Unexpected constructor: "+term.c);
  }
  return true;
}

// Check that a and b have compatible head. Stacks conversion-relevant subterms in t.
function same_head_with_depth(a,b,d,acc) {
  if (a.c !== b.c) { return false; }
  switch (a.c) {
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
    default: fail("Equals","Unexpected constructor: "+term.c);
  }
  return true;
}

function equals(u, v) {
  const acc = [ [u,v] ];
  while (acc.length > 0) {
    const [a,b] = acc.pop();
    if (a === b) { continue; }
    if (!same_head(a,b,acc)) { return false; }
  }
  return true;
}

/** Substitutes [val] for variable with DeBruijn index [depth]
 *  and downshifts all variables referencing beyond that index:
 *    subst(  y#0 \x.(x#0 y#1 z#2) , v#9 )  :=  v#8 \x.(x#0 v#9 z#1)
 */
function subst(term, val, depth=0) {
  // Shifts memoisation
  const shifts = [val];
  function s(t,d) {
    switch (t.c) {
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

/** Substitutes each [vals[i]] for variables with DeBruijn index [depth+i]
 *  and downshifts all variables referencing beyond that index:
 * subst(  y#0 \x.(x#0 y#1 z#2) , v#9 )  :=  v#8 \x.(x#0 v#9 z#1)
 * Lazily applies the function [to_term] at most one to all vals
 */
function subst_l(term, vals, depth=0, to_term=(t)=>t) {
  // Shifts memoisation
  const shifts_arr = Array(vals.length).fill([]);
  const nbvals = vams.length;
  function s(t,d) {
    switch (t.c) {
      case "Var":
        nbvals
        if (t.index >= d+nbvals) {
          return Var(t.index - nbvals);
        } else if (t.index < d) {
          return t;
        } else {
          const shifts = shifts_arr[t.index-d];
          if (!shifts[d]) {
          if (!shifts.length) { shifts[0] = to_term( vals[t.index-d] ); }
            shifts[d] = shift(shifts[0] ,inc=d);
          }
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


// Note : meta-substitution are done "by name" > avoid capture !
//     f X[] Y[] { X => t, Y => u } --> f t u
// meta-variable instantiation is done "by DB index"
//     X[t,u] { X[x,y] => f x y } --> f x[0] y[1] { [0] => t, [1] => u }

/** Checks that given term array [args] are distinct locally bounded variables [a_0, ..., a_n]
    Returns an array A such that:
    - A[a_i] is an unnamed var of index i
    - A[b] is undefined for all variables b distinct from the a_i
    Example:
    Input:
      args = [ z[2], y[0] ]
      depth = 3
    Ouput:
      [ 1, undefined, 0 ]
*/
function get_meta_match(args, depth) {
  const res = new Array(depth);
  args.forEach( function (a,i) {
    if (a.c !== 'Var' || a.index >= depth) {
      fail("MetaMatch","Expected a locally bounded variable, got:"+pp_term(a));
    } else if (res[a.index] != undefined) {
      fail("MetaMatch","Expected distinct variables, got "+pp_term(a)+"twice");
    } else {
      res[a.index] = i;
    }
  });
  return res;
}

/** Matches all variables in [term] to the corresponding meta variable in [map]
    Variables beyond [depth] are shifted down by [depth], others raise an error if unmatched.
    Example:
      Input:
        term = x:A -> f x[0] y[1] z[3] u[4]
        map = [ 1, undefined, 0 ]
        arity = 2
        depth = 3
      Output:
        x:A -> f x[0] ?[2] ?[1] u[3]
      This would be used to perform to the matching of the term
      again some pattern X[ z[2], y[0] ]
*/
function meta_match(term, map, arity, depth) {
  if (depth == 0) { return term; }
  function mm(t,d) {
    switch (t.c) {
      case "Var":
        if (t.index < d) { return t; }
        if (t.index >= d + depth) { return Var(t.index-depth+arity, t.preferred_name); }
        const i = map[t.index - d];
        if (i === undefined) {
          fail('MetaMatchFailed',"Unexpected locally bounded variable ["+pp_term(t)+"]." );
        } else {
          return Var(i+d);
        }
      case "All" : return All(t.name, mm(t.dom,d), mm(t.cod,d+1));
      case "Lam" : return Lam(t.name, t.type && mm(t.type,d) , mm(t.body,d+1) );
      case "App" : return App( mm(t.func,d) , mm(t.argm,d) );
      case "MVar": return MVar(t.name, t.args.map( (t)=>mm(t,d) ));
      default: return t;
    }
  }
  return mm(term,0);
}
