
// Returns [term] where each free variables instance x#0 in turned into a meta-variable
// whose name !3 corresponds to its DeBruijn *level*. (assuming ctx_size=4 in the example)
function vars_to_meta(term:Term, ctx_size:number, depth=0) : Term {
  function s(t:Term, d:number) : Term {
    switch (t.c) {
      case "Var" : return t.index < d ? t: MVar('!'+(ctx_size - 1 - t.index + d));
      case "All" : return All(t.name, s(t.dom,d) , s(t.cod,d+1) );
      case "Lam" : return Lam(t.name, t.type && s(t.type,d) , s(t.body,d+1) );
      case "App" : return App( s(t.func,d) , s(t.argm,d) );
      case "MVar": return MVar(t.name, t.args.map( (t:Term) => s(t,d) ) );
      default: return t;
    }
  }
  return s(term,depth);
}


/** For all [args] = [t_0, ..., t_n]
    Returns the substitution { t_i : i | t_i is a variable below depth [depth] }
*/
function get_partial_meta_match(args:Term[], depth:number) : { [k:number] : number } {
  const res : { [key: number] : number } = {};
  args.forEach( function(a,i) {
    if (a.c === 'Var' && a.index < depth) {
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
function meta_match(term:Term, map:{ [k:number] : number }, arity:number, depth:number) : Term {
  if (depth == 0) { return term; }
  function mm(t:Term, d:number) : Term {
    switch (t.c) {
      case "Var":
        if (t.index < d) { return t; }
        if (t.index >= d + depth) { return Var(t.index-depth+arity, t.preferred_name); }
        const i = map[t.index - d];
        if (i === undefined) {
          fail('MetaMatchFailed',"Unexpected locally bound variable ["+pp_term(t)+"]." );
        } else {
          return Var(i+d);
        }
      case "All" : return All(t.name, mm(t.dom,d), mm(t.cod,d+1));
      case "Lam" : return Lam(t.name, t.type && mm(t.type,d) , mm(t.body,d+1) );
      case "App" : return App( mm(t.func,d) , mm(t.argm,d) );
      case "MVar": return MVar(t.name, t.args.map( (t:Term) => mm(t,d) ));
      default: return t;
    }
  }
  return mm(term,0);
}

/** Checks whether the given term is a non-pattern meta-variable instance.
*/
function is_non_pattern_instance(term:Term) {
  // Applied meta-variable are offending
  if (term.c === 'App') {
    return term.func.c === 'MVar';
  }
  // A meta-var instance is offending if either:
  // - one arguments was not a var (null in the bag)
  // - the number of distincts areguments is less than the number of arguments
  if (term.c === 'MVar') {
    // We collect the DB index of all arguments that are variables
    const bag = new Set();
    term.args.forEach( (a:Term) => bag.add(a.c==="Var" ? a.index : null));
    return bag.has(null) || bag.size < term.args.length;
  }
  return false;
}


/** Meta-variables substitution
 *
 * Relies on a map associating each meta-variable name
 * to (an array of memoised shifted) term(s) with which to substitute.
 */
function meta_map_subst(term:Term, subst : Map<string,Term>, depth=0) : Term {
  // Shift memoisation : maps metavar name to multiple shifted values
  let ct = 0; // Compteur de substitutions
  const map : Map<string,Term[]> = new Map();
  subst.forEach((v,k)=>map.set(k,[v]));
  function ms(t:Term, d:number) {
    const cta = ct;
    if (t.c === "MVar") {
      const args = t.args.map((t:Term)=>ms(t,d));
      const shifts = map.get(t.name);
      if (!shifts) { return (ct === cta ? t : MVar(t.name,args)); }
      ct += 1; // Substitution effectuée
      if ( !(shifts instanceof Array) ) {
        return meta_map_subst(shifts, args);
      } else if (!shifts[d]) {
        shifts[d] = shift(shifts[0], d);
      }
      return meta_map_subst(shifts[d], args);
    } else if (t.c === "All") {
      const dom : Term = ms(t.dom, d  );
      const cod : Term= ms(t.cod, d+1);
      return (ct === cta && t) || All(t.name, dom, cod);
    } else if (t.c === "Lam") {
      const type : Term= t.type && ms(t.type, d  );
      const body : Term=           ms(t.body, d+1);
      return (ct === cta && t) || Lam(t.name,type,body);
    } else if (t.c === "App") {
      const func : Term= ms(t.func,d);
      const argm : Term= ms(t.argm,d);
      return (ct === cta && t) || App(func,argm);
    } else {
      return t;
    }
  }
  return ms(term,depth);
}

type TypeAssumption =  {
  name : string,
  ctx  : Term[],
  args : string[],
  type : Term
}

// Typing and convertion assumptions mechanisms
class AssumptionSet {
  red: ReductionEngine;
  assumed_types : TypeAssumption[] = [];
  assumed_conv : [Term,Term][] = [];
  // Progressively build a variable substitution
  subst : Map<any,any> = new Map();

  constructor(red: ReductionEngine) { this.red = red; }

  is_injective(t:Term) {
    return t.c==='Var' || (t.c==='Ref' && this.red.is_injective(t.name));
  }
  
  equals(u:Term, v:Term) {
    return equals(u, v) ||
      this.assumed_conv.some(function ([a,b]:[Term,Term]) {
        return (equals(a, u) && equals(b, v)) || (equals(a, v) && equals(b, u));
      });
  }
  
  // Check wether the terms can be decided convertible using the given assumptions
  are_convertible(u:Term, v:Term) {
    const acc :[Term,Term][] = [ [ this.msubst(u), this.msubst(v)] ];
    let top;
    while (top = acc.pop()) {
      const [a,b] = top;
      //console.log("Conv:",pp_term(a),"<<-?->>",pp_term(b));
      if (!this.equals(a,b)) {
        const whnf_a = this.red.whnf(a);
        const whnf_b = this.red.whnf(b);
        if (!this.equals(whnf_a,whnf_b)) {
          if (!same_head(whnf_a, whnf_b, acc)) {
            //console.log("Mismatch: ",pp_term(whnf_a)," <-/-> ", pp_term(whnf_b));
            return false;
          }
        }
      }
    }
    return true;
  }

  msubst(t:Term) : Term { return meta_map_subst(t, this.subst); }

  // Check where the terms can be decided convertible using the given assumptions
  // And assuming meta-variable !j for j < i can be substituted (in the LHS only)
  // The meta-substitution S is updated with the required substitutions
  // if [i] is omitted : all variables !j can be substituted
  are_convertible_unify(u:Term, v:Term, S:Map<string,Term>, i?:number) {
    // Stack of required conversion check together with their depth (used for unifications)
    const acc : [Term, Term, number][] = [ [this.msubst(u), this.msubst(v), 0] ];
    let top;
    while (top = acc.pop()) {
      const [a,b,d] = top;
      //console.log("ConvU:",pp_term(a),"<<-?->>",pp_term(b));
      if (equals(a,b)) { continue; }
      const whnfa = this.red.whnf(a);
      if (whnfa.c==='MVar' && /^![0-9]+$/.test(whnfa.name)) {
        const index = parseInt(whnfa.name.substring(1));
        if (i !== undefined && index >= i) { fail('ConvCheck RHS','This should not happen'); }
        const match = meta_match(b, get_partial_meta_match(whnfa.args, d), whnfa.args.length, d);
        // Extend the substitution S
        S.set(whnfa.name, match);
        // Apply the extended S to the LHS of the remaining conversion checks
        acc.forEach(function(c) { c[0] = meta_map_subst(c[0],S); });
        continue;
      }
      if (!same_head_with_depth(whnfa, this.red.whnf(b), d,acc)) { return false; }
    }
    return true;
  }

  // Find a WHNF using the assumptions to substitute meta-variables
  whnf(term:Term) : Term { return this.red.whnf( this.msubst(term) ); }

  // Extend the substitution with {x => t}
  extend_subst(x:string, t:Term) {
    // apply current meta-substitution to b
    const val = this.msubst(t);
    // Build the meta-subst {X => b}
    const aux = new Map([[x, val]]);
    // Apply {X => b} to the current substitution
    this.subst.forEach((v,k)=> this.subst.set(k, meta_map_subst(v,aux)) );
    // Extend the substitution
    this.subst.set(x, val);
    // Forget all previous assumptions
    const prev_assumptions = this.assumed_conv;
    this.assumed_conv = [];
    // Re-assume them, substituted with {X => b} to both sides
    prev_assumptions.forEach( ([a,b]:[Term,Term]) => this.assume_convertible(this.whnf(a),this.whnf(b)));
  }

  // Assume a new convertibility a == b
  assume_conv(a:Term, b:Term) {
    if (a.c==='MVar' && !this.subst.has(a.name)) {
      // If a is a new meta-var, then extend the substitution
      this.extend_subst(a.name,b);
    } else {
      // Else simply add the (substituted) equation
      // It may be later used to extend the substitution
      this.assumed_conv.push([a,b]);
    }
  }


  // Record an assumed convertibility between two terms
  assume_convertible(t1:Term, t2:Term) {
    const acc = [[t1,t2]];
    // We record information from this assumed conversion
    // and only return a false-value if the given terms can never be convertible
    // (warn the user that something is off...)
    let top;
    while (top = acc.pop()) {
      const [u,v] = top;
      if (equals(u,v)) { continue; }
      const a = this.whnf(u);
      const b = this.whnf(v);
      if      (a.c === 'MVar') { this.assume_conv(a,b); }
      else if (b.c === 'MVar') { this.assume_conv(b,a); }
      else if (a.c !== b.c)   { this.assume_conv(a,b); }
      else if (a.c === "All") {
        acc.push([a.dom,b.dom] , [a.cod,b.cod]);
      } else if (a.c === "Lam") {
        acc.push([a.body,b.body]);
      } else if (a.c === "App") {
        const [head_a, args_a] = get_head(a);
        const [head_b, args_b] = get_head(b);
        if (equals(head_a,head_b) && this.is_injective(head_a)) {
          if (args_a.length !== args_b.length) {
            fail('LHS Conversion Check',
              'Non unifiable terms: `'+pp_term(a)+"` and `"+pp_term(b)+"`.");
          } else {
            for (let i = 0; i < args_a.length; i++) {
              acc.push([args_a[i],args_b[i]]);
            }
          }
        } else {
          this.assume_conv(a,b);
        }
      }
    }
  }

  
  // Record a new type assumption
  assume_mvar_type(term:Term, expected_type:Term, ctx:Ctxt) {
    const acc : Term[] = [];
    while (ctx) { acc.push(ctx.head[1]); ctx = ctx.tail; }
    acc.reverse();
    this.assumed_types.push(
      {
        name : term.name,
        ctx  : acc.map((x,i)=> vars_to_meta(x,i)),
        args : term.args.map( (t:Term) =>'!'+(acc.length-t.index-1)),
        type : vars_to_meta(expected_type,acc.length),
      });
  }

  pp() {
    let res = "\n[ASSUMED TYPES]\n";
    this.assumed_types.forEach(function(a) {
      res += a.ctx.map((t,i)=> "!"+i+" : "+pp_term(t)).join(", ")+ "  |-  " +
        a.name+"["+ a.args.join(', ')+"] : "+pp_term(a.type)+"\n";
    });
    res += "\n[ASSUMED CONVERSIONS]\n"+
      this.assumed_conv.map(([a,b]) => pp_term(a)+" == "+pp_term(b)).join('\n');
    return res;
  }
}

// Rule checking entry point
class RuleChecker {
  red : ReductionEngine;
  env : Environment;

  constructor(env:Environment, red:ReductionEngine) {
    this.env = env;
    this.red = red;
  }

  //////////////////////////////////////////////////////////////
  //////   Typing and convertion assumptions mechanisms  ///////
  //////////////////////////////////////////////////////////////

  // Returns the first inferred type for metavariable [term] = X[a_0, ..., a_n]
  // The typing assumptions are scanned to find one that allows to infer a type for [term]
  // for some substitution S of the locally bound variables
  // If [expected_type] is provided then the inferred type is checked to be unifiable with it
  // for some extension of S
  rhs_infer_mvar_type(assumptions:AssumptionSet, term:Term, ctx:Ctxt, expected_type?:Term) {
    //console.log("RHS Infer MVar: Inferring the type of meta-variable instance `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx) + assumptions.pp());
    for (let k = 0; k < assumptions.assumed_types.length; k++) {
      const assumption = assumptions.assumed_types[k];
      if (assumption.name !== term.name) { continue; }
      const arity = assumption.args.length;
      const ctx_size = assumption.ctx.length;
      // Build the variable substitution
      //   S = { assumption.args => term.args (shifted by position in assumption.ctx) }
      const S = new Map();
      for(let i = 0; i < assumption.args.length; i++) {
        S.set(assumption.args[i], term.args[i]);
      }
      // Check that it preserves
      // the well-typedness of assumption.ctx
      // Example : if   x:A , y:B[x], z:C[x,y], w:D[x,y,z]    with   S={z -> t}
      // Then progressively build a "variable substitution"
      // i.e. such that #2 is mapped to t[#0, #1] (out of scope vars are constants so ok)
      // Check that :
      //   - t:C[x,y] for some x=u, and y=v
      //   - v:B[x] for some x=v' == v
      //   - u:A
      // Build assumption.type substituted with S and with the variable substitution (with substitute shifted)
      // Unshift it to ensure contains no remaining variable and return it
      try {
        const unchecked : boolean[] = Array(ctx_size).fill(true);
        function aux(self:RuleChecker) {
          // Find the first unchecked variable that is mapped to something in S
          const i = unchecked.findIndex((t,i)=>t && S.has('!'+i));
          if (i < 0) { return true; } // if there are none, then the work is done: proceed
          // else compute the expected type substituted with the partial substitution S
          
          // Check that this value S[i] has the expected type...
          // ... for some assignation of the variables j<i in S !
          const type_of_ith = meta_map_subst(assumption.ctx[i],S);
          self.rhs_check_unify(assumptions, S.get('!'+i), type_of_ith, ctx, S, i);
          unchecked[i] = false; // Never check this index again
        }
        while (!aux(this)) {}
        const inf_final_type = meta_map_subst(assumption.type, S);
        if (expected_type === undefined) { // Infer mode
          return inf_final_type;
        } else { // Check mode
          // If we need to check a type for the result, then unify the inferred one
          // allowing for even further extension of S
          if (!assumptions.are_convertible_unify(inf_final_type, expected_type, S)) { throw("[rhs_infer_mvar_type] This should not escape"); }
          // check that the extension of S is still ok (might require even further extension of S)
          while (!aux(this)) {}
          return; // The check is successful, return
        }
      } catch (e) {} // Ignore errors and proceed with the next assumption instead
    }
    fail("RHS Infer","Cannot infer the type of meta-variable instance `" +
      pp_term(term, ctx) + "`.\n" + pp_context(ctx) + assumptions.pp());
  }
  

  //////////////////////////////////////////////////////////////
  ////////////////////       LHS  Checking  ////////////////////
  //////////////////////////////////////////////////////////////

  // Infers the type of a term
  lhs_infer(assumptions:AssumptionSet, term:Term, ctx:Ctxt = null) {
    //console.log("LHS Infer",pp_term(term,ctx));
    switch (term.c) {
      case "Knd": fail("LHS Infer","Cannot infer the type of Kind !");
      case "Typ": return Knd();
      case "All":
        const dom_sort = assumptions.whnf( this.lhs_infer(assumptions, term.dom, ctx) );
        const cod_sort = assumptions.whnf( this.lhs_infer(assumptions, term.cod, extend(ctx, [term.name, term.dom])) );
        if (dom_sort.c !== "Typ") {
          fail("LHS Infer","Domain of forall is not a type: `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        if (cod_sort.c !== "Typ" && cod_sort.c !== "Knd") {
          fail("LHS Infer","Codomain of forall is neither a type nor a kind: `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        return cod_sort;
      case "Lam":
        if (term.type === null) {
          fail("LHS Infer","Can't infer non-annotated lambda `" +
            pp_term(term,ctx)+"`.\n" + pp_context(ctx));
        } else {
          const body_t = this.lhs_infer(assumptions, term.body, extend(ctx, [term.name, term.type]));
          const term_t = All(term.name, term.type, body_t);
          this.lhs_infer(assumptions, term_t, ctx);
          return term_t;
        }
      case "App":
        const func_t = assumptions.whnf(this.lhs_infer(assumptions, term.func, ctx));
        // Technically we don't need to fail here : if we can't infer a product type
        // then we can just ignore the rest of the typing of this LHS subterm
        // or just check that term.argm is well-typed (with any type).
        // We should probably at least warn that something looks weird though.
        if (func_t.c !== "All") {
          fail("LHS Infer","Non-function application on `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        this.lhs_check(assumptions, term.argm, func_t.dom, ctx);
        return subst(func_t.cod, term.argm);
      case "Ref": return this.env.do_get(term.name).type;
      case "Var": return get_term(ctx, term.index);
      case "MVar":
        fail("LHS Check", "Could not infer the type of meta-variable instance `"+
          pp_term(term, ctx)+"`.\nThis should not happen... LHS is probably ill-formed (?)\n"+
          pp_context(ctx)+ + assumptions.pp());
      default:
        // We could just warn and proceed but this case should only happen in weird cases...
        fail("LHS Infer", "Unable to infer type of `" +
          pp_term(term, ctx) + "`.\n" + pp_context(ctx));
    }
  }

  // Checks if a term has given expected type
  lhs_check(assumptions:AssumptionSet, term:Term, expected_type:Term, ctx:Ctxt = Ctx()) {
    //console.log("LHS Check "+pp_term(term,ctx)+" has type "+pp_term(expected_type,ctx));
    if (term.c === 'MVar') {
      assumptions.assume_mvar_type(term, expected_type, ctx);
    } else {
      const type = assumptions.whnf(expected_type);
      if (type.c === "All" && term.c === "Lam") {
        if (!term.type.joker) { fail("LHS Check", "Please avoid type annotations in LHS..."); }
        this.lhs_infer(assumptions, type.dom, ctx);
        this.lhs_check(assumptions, term.body, type.cod, extend(ctx, [type.name, type.dom]) );
      } else {
        assumptions.assume_convertible(type, this.lhs_infer(assumptions, term, ctx));
      }
    }
  }


  //////////////////////////////////////////////////////////////
  ////////////////////       RHS  Checking  ////////////////////
  //////////////////////////////////////////////////////////////

  // Infers the type of a RHS meta-term assuming the given assumptions
  // (that were inferred from typing the LHS)
  rhs_infer(assumptions:AssumptionSet, term:Term, ctx=Ctx()) {
    //console.log("RHS Infer",term.c,term,pp_term(term,ctx));
    switch (term.c) {
      case "Knd": fail("RHS Infer","Cannot infer the type of Kind !");
      case "Typ": return Knd();
      case "All":
        const dom_sort = assumptions.whnf( this.rhs_infer(assumptions, term.dom, ctx) );
        const cod_sort = assumptions.whnf( this.rhs_infer(assumptions, term.cod, extend(ctx, [term.name, term.dom])) );
        if (dom_sort.c !== "Typ") {
          fail("RHS Infer","Domain of forall is not a type: `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx)+ assumptions.pp());
        }
        if (cod_sort.c !== "Typ" && cod_sort.c !== "Knd") {
          fail("RHS Infer","Codomain of forall is neither a type nor a kind: `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx)+ assumptions.pp());
        }
        return cod_sort;
      case "Lam":
        if (term.type === null || (term.type.c == 'MVar' && term.type.joker) ) {
          fail("Infer","Can't infer unannotated lambda `" +
            pp_term(term,ctx) + "`.\n" + pp_context(ctx)+ assumptions.pp());
        } else {
          const body_t = this.rhs_infer(assumptions, term.body, extend(ctx, [term.name, term.type]));
          const term_t = All(term.name, term.type, body_t);
          this.rhs_infer(assumptions, term_t, ctx);
          return term_t;
        }
      case "App":
        const func_t = assumptions.whnf(this.rhs_infer(assumptions, term.func, ctx));
        if (func_t.c !== "All") {
          fail("RHS Infer","Non-function application on `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx) + assumptions.pp());
        }
        this.rhs_check(assumptions, term.argm, func_t.dom, ctx);
        return subst(func_t.cod, term.argm);
      case "Ref": return this.env.do_get(term.name).type;
      case "Var":
        const ctxt_type = get_term(ctx, term.index);
        if(!ctxt_type) {
          fail("RHS Infer","Cannot infer the type of free variable `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx) + assumptions.pp());
        }
        return ctxt_type;
      case "MVar": return this.rhs_infer_mvar_type(assumptions, term, ctx);
      default:
        fail("RHS Infer","Unable to infer type of `" +
          pp_term(term, ctx) + "`.\n" + pp_context(ctx) + assumptions.pp());
    }
  }

  // Check the type of a RHS meta-term assuming the given assumptions
  // (that were inferred from typing the LHS)
  rhs_check(assumptions:AssumptionSet, term:Term, expected_type:Term, ctx=Ctx()) {
    //console.log("CheckWithAssumption",pp_term(term,ctx), pp_term(expected_type,ctx));
    const type = assumptions.whnf(expected_type);
    if (type.c === "All" && term.c === "Lam") {
      this.rhs_infer(assumptions, type, ctx);
      if (term.type.joker) {
        term.type = type.dom;
      } else if (!assumptions.are_convertible(term.type, type.dom)) {
        fail("RHS Check", "Incompatible annotation `"+pp_term(term, ctx)+"`.\n"+
          "- Expect = " + pp_term(type.dom , ctx)+"\n"+
          "- Actual = " + pp_term(term.type, ctx)+"\n"+
          pp_context(ctx) + assumptions.pp());
      } else {
        this.rhs_infer(assumptions, type.dom, ctx);
      }
      this.rhs_check(assumptions, term.body, type.cod, extend(ctx, [type.name, type.dom]));
    } else if (term.c === "MVar") {
      this.rhs_infer_mvar_type(assumptions, term, ctx, type); // This call is actually a check
    } else {
      const term_t = this.rhs_infer(assumptions, term, ctx);
      if (!assumptions.are_convertible(type, term_t)) {
        fail("RHS Check", "Type mismatch on `"+pp_term(term, ctx)+"`.\n"+
          "- Expect = " + pp_term(type  , ctx)+"\n"+
          "- Actual = " + pp_term(term_t, ctx)+"\n"+
          pp_context(ctx) + assumptions.pp());
      }
    }
  }


  //////////////////////////////////////////////////////////////
  /////////////   RHS  Checking with Unification   /////////////
  //////////////////////////////////////////////////////////////

  // Infers the type of a RHS meta-term assuming the given assumptions
  // (that were inferred from typing the LHS)
  rhs_infer_unify(assumptions:AssumptionSet, term:Term, ctx:Ctxt, S:Map<string,Term>, i:number) {
    //console.log("RHS Infer Unify",term.c,term,pp_term(term,ctx));
    switch (term.c) {
      case "Knd": fail("RHS Infer Unify","Cannot infer the type of Kind !");
      case "Typ": return Knd();
      case "All":
        const dom_sort = assumptions.whnf( this.rhs_infer_unify(assumptions, term.dom, ctx, S, i) );
        const cod_sort = assumptions.whnf( this.rhs_infer_unify(assumptions, term.cod, extend(ctx, [term.name, term.dom]), S, i) );
        if (dom_sort.c !== "Typ") {
          fail("RHS Infer Unify","Domain of forall is not a type: `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx)+ assumptions.pp());
        }
        if (cod_sort.c !== "Typ" && cod_sort.c !== "Knd") {
          fail("RHS Infer Unify","Codomain of forall is neither a type nor a kind: `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx)+ assumptions.pp());
        }
        return cod_sort;
      case "Lam":
        if (term.type === null || (term.type.c == 'MVar' && term.type.joker) ) {
          fail("RHS Infer Unify","Can't infer unannotated lambda `" +
            pp_term(term,ctx) + "`.\n" + pp_context(ctx)+ assumptions.pp());
        } else {
          const body_t = this.rhs_infer_unify(assumptions, term.body, extend(ctx, [term.name, term.type]), S, i);
          const term_t = All(term.name, term.type, body_t);
          this.rhs_infer_unify(assumptions, term_t, ctx, S, i);
          return term_t;
        }
      case "App":
        const func_t = assumptions.whnf(this.rhs_infer_unify(assumptions, term.func, ctx, S, i));
        if (func_t.c !== "All") {
          fail("RHS Infer Unify","Non-function application on `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx) + assumptions.pp());
        }
        this.rhs_check_unify(assumptions, term.argm, func_t.dom, ctx, S, i);
        return subst(func_t.cod, term.argm);
      case "Ref": return this.env.do_get(term.name).type;
      case "Var":
        const ctxt_type = get_term(ctx, term.index);
        if(!ctxt_type) {
          fail("RHS Infer Unify","Cannot infer the type of free variable `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx) + assumptions.pp());
        }
        return ctxt_type;
      case "MVar": return this.rhs_infer_mvar_type(assumptions, term, ctx);
      default:
        fail("RHS Infer Unify","Unable to infer type of `" +
          pp_term(term, ctx) + "`.\n" + pp_context(ctx) + assumptions.pp());
    }
  }

  // Check the type of a RHS meta-term assuming the given assumptions
  // (that were inferred from typing the LHS)
  // Allows to perform unification in S
  rhs_check_unify(assumptions:AssumptionSet, term:Term, expected_type:Term, ctx:Ctxt, S:Map<string,Term>, i:number) {
    //console.log("CheckWithAssumption",pp_term(term,ctx), pp_term(expected_type,ctx));
    const type = assumptions.whnf(expected_type);
    if (type.c === "All" && term.c === "Lam") {
      this.rhs_infer_unify(assumptions, type, ctx, S, i);
      if (term.type.joker) {
        term.type = type.dom;
      } else if (!assumptions.are_convertible_unify(term.type, type.dom, S, i)) {
        fail("RHS Check Unify", "Incompatible annotation `"+pp_term(term, ctx)+"`.\n"+
          "- Expect = " + pp_term(type.dom , ctx)+"\n"+
          "- Actual = " + pp_term(term.type, ctx)+"\n"+
          pp_context(ctx) + assumptions.pp());
      } else {
        this.rhs_infer_unify(assumptions, type.dom, ctx, S, i);
      }
      this.rhs_check_unify(assumptions, term.body, type.cod, extend(ctx, [type.name, type.dom]), S, i);
    } else {
      const term_t = this.rhs_infer_unify(assumptions, term, ctx, S, i);
      if (!assumptions.are_convertible_unify(type, term_t, S, i)) {
        fail("RHS Check Unify", "Type mismatch on `"+pp_term(term, ctx)+"`.\n"+
          "- Expect = " + pp_term(type  , ctx)+"\n"+
          "- Actual = " + pp_term(term_t, ctx)+"\n"+
          pp_context(ctx) + assumptions.pp());
      }
    }
  }

  //////////////////////////////////////////////////////////////
  ////////////////////       Rule  Checking  ///////////////////
  //////////////////////////////////////////////////////////////

  check_rule_well_formed(rule:ExRule) {
    if (!is_closed(rule.lhs)) { fail("Rule","LHS must be a closed term."); }
    if (!is_closed(rule.rhs)) { fail("Rule","RHS must be a closed term."); }
    // A pattern is ill-formed if a subterm is a non-pattern or applied meta-variable instance
    const nonpattern = find_subterm(is_non_pattern_instance, rule.lhs);
    if (nonpattern) {
      fail("Rule","Meta-vars in LHS must only be applied to distinct variables `"+
        pp_term(nonpattern[0],nonpattern[1]) + "`.");
    }
    // A pattern is ill-formed if a meta-variable occurs with distinct arities
    const arities = new Map();
    const check_mvar = function(t:Term) : boolean {
      if(t.c === 'MVar') {
        if (arities.has(t.name) && arities.get(t.name)!==t.args.length) { return true; }
        arities.set(t.name, t.args.length);
      }
      return false;
    }
    const wrong_arity_instance = find_subterm(check_mvar, rule.lhs) || find_subterm(check_mvar, rule.rhs);
    if (wrong_arity_instance) {
      fail("Rule","Meta-vars occurs with several distinct arities `"+
        pp_term(wrong_arity_instance[0],wrong_arity_instance[1]) + "`.");
    }
  }

  check_rule_type_preservation(rule:ExRule) {
    if (!rule.check) { return; }
    const assumptions = new AssumptionSet(this.red);
    const inferred_type = this.lhs_infer(assumptions, rule.lhs);
    this.rhs_check(assumptions, rule.rhs, inferred_type);
  }

  // Checks type preservation and add a new rule to the reduction machine
  declare_rule(rule:ExRule) {
    const [hd,tl] = get_head(rule.lhs);
    if (hd.c!=="Ref") { fail("Rule","LHS must be headed by a symbol."); }
    const smb = this.env.get(hd.name);
    if (smb.proof) {
      if (smb.proven) { fail("Rule","Proof `"+smb.name+"` already provided."); }
      if (tl.length > 0) { fail("Rule","Proof must be defined unapplied."); }
    }
    this.check_rule_well_formed(rule);
    this.check_rule_type_preservation(rule);
    this.red.add_new_rule(rule);
    if (smb.proof) { smb.proven=true; }
  }
}
