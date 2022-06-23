

// Returns [term] where each free variables instance x#0 in turned into a meta-variable
// whose name !3 corresponds to its DeBruijn *level*. (assuming ctx_size=4 in the example)
function vars_to_meta(term, ctx_size, depth=0) {
  function s(t,d) {
    switch (t[c]) {
      case "Var" : return t.index < d ? t: MVar('!'+(ctx_size - 1 - t.index + d));
      case "All" : return All(t.name, s(t.dom,d) , s(t.cod,d+1) );
      case "Lam" : return Lam(t.name, t.type && s(t.type,d) , s(t.body,d+1) );
      case "App" : return App( s(t.func,d) , s(t.argm,d) );
      case "MVar": return MVar(t.name, t.args.map((t)=>s(t,d)) );
      default: return t;
    }
  }
  return s(term,depth);
}


// Checks whether the given term is a non-pattern meta-variable instance.
function is_non_pattern_instance(term) {
  // Applied meta-variable are offending
  if (term[c] === 'App') {
    return term.func[c] === 'MVar';
  }
  // A meta-var instance is offending if either:
  // - one arguments was not a var (null in the bag)
  // - the number of distincts areguments is less than the number of arguments
  if (term[c] === 'MVar') { 
    // We collect the DB index of all arguments that are variables
    const bag = new Set();
    term.args.forEach(a => bag.add(a[c]==="Var" ? a.index : null));
    return bag.has(null) || bag.size < term.args.length;
  }
  return false;
}

// Typing and convertion assumptions mechanisms
class Assumptions {
  constructor(sig) {
    this.sig = sig;
    this.assumed_types = [];
    this.assumed_conv = [];
  }
  
  pp() {
    let res = "\n[ASSUMED TYPES]\n";
    this.assumed_types.forEach(function(a) {
      res += a.ctx.map((t,i)=> "!"+i+" : "+pp_term(t)).join(", ")+ "  |-  " +
        a.name+"["+ a.args.join(', ')+"] : "+pp_term(a.type)+"\n";
    });
    res += "\n[ASSUMED CONVERSIONS]\n";
    return res;
  }
}


// Rule checking entry point
class RuleChecker {
  
  constructor(sig) {
    this.sig = sig;
    this.env = sig.env;
    this.red = sig.red;
  }
  
  //////////////////////////////////////////////////////////////
  //////   Typing and convertion assumptions mechanisms  ///////
  //////////////////////////////////////////////////////////////
  
  //TODO: move what is possible to Assumptions...
  
  // Record a new type
  assume_mvar_type(assumptions,term, expected_type, ctx) {
    const acc = [];
    while (ctx) { acc.push(ctx.head[1]); ctx = ctx.tail; }
    assumptions.assumed_types.push(
      {
        name : term.name,
        ctx  : acc.map((x,i)=> vars_to_meta(x,i)),
        args : term.args.map(t=>'!'+(acc.length-t.index-1)),
        type : vars_to_meta(expected_type,acc.length),
      });
  }
  
  // Record a conversion
  assume_convertible(assumptions, t1, t2) {
    // TODO : we should record information from this assumed conversion
    // and only return a false-value if the given terms can never be convertible
    // (warn the user that something is off...)
    const acc = [ [t1,t2] ];
    while (acc.length > 0) {
      const [u,v] = acc.pop();
      if (equals(u,v)) { continue; }
      const a = this.red.whnf(u);
      const b = this.red.whnf(v);
      if (a[c] === 'MVar') { assumptions.assumed_conv.push(a,b); continue; }
      if (b[c] === 'MVar') { assumptions.assumed_conv.push(b,a); continue; }
      if (a[c] !== b[c]) { continue; }
      if (a[c] === "All") {
        acc.push([a.dom,b.dom] , [a.cod,b.cod]);
      } else if (a[c] === "Lam") {
        acc.push([a.body,b.body]);
      } else if (a[c] === "App") {
        const [head_a, args_a] = get_head(a);
        const [head_b, args_b] = get_head(b);
        if (equals(head_a,head_b) && this.sig.is_injective(head_a)) {
          if (args_a.length !== args_b.length) {
            fail('LHS Conversion Check',
              'Non unifiable terms: `'+pp_term(a)+"` and `"+pp_term(b)+"`.");
          } else {
            for (let i = 0; i < args_a.length; i++) {
              acc.push([args_a[i],args_b[i]]);
            }
          }
        }
      }
    }
  }
  
  // Check wether the term can be decided convertible using the assumptions
  are_convertible(assumptions, t1, t2) {
    // extend to use the recorded assumptions
    return this.red.are_convertible(t1, t2);
  }
  
  // Find a WHNF using the assumption to get a product type ("All") if possible
  whnf(assumptions, term) {
    return this.red.whnf(term);
  }
  
  // Note: should rather return a list of possible types
  rhs_infer_mvar_type(assumptions, term, ctx) {
    for (let k = 0; k < assumptions.assumed_types.length; k++) {
      
      const assumption = assumptions.assumed_types[k];
      if (assumption.name !== term.name) { continue; }
      const arity = assumption.args.length;
      const ctx_size = assumption.ctx.length;
      // Build the variable substitution
      //   S = { assumption.args => term.args (shifted by position in assumption.ctx) }
      const S = new Map();
      for(let i = 0; i < assumption.args.length; i++) {
        S[assumption.args[i]] = term.args[i];
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
        const unchecked = Array(ctx_size).fill(true);
        while (true) {
          // Find the first unchecked variable that is mapped to something in S
          const i = unchecked.findIndex((t,i)=>t && S['!'+i]);
          if (i < 0) { break; } // if there are none, then the work is done: proceed
          // else compute the expected type substituted with the partial substitution S
          const type_of_ith = meta_subst(assumption.ctx[i],S);
          // TODO : better implement this check
          this.rhs_check(assumptions, S['!'+i], type_of_ith);
          unchecked[i] = false; // Never check this index again
        }
        return meta_subst(assumption.type,S);
      } catch (e) { throw e; }
    }
    fail("RHS Infer","Cannot infer the type of meta-variable instance `" +
      pp_term(term, ctx) + "`.\n" + pp_context(ctx) + assumptions.pp());
  }
  
  
  //////////////////////////////////////////////////////////////
  ////////////////////       LHS  Checking  ////////////////////
  //////////////////////////////////////////////////////////////
  
  // Infers the type of a term
  lhs_infer(assumptions, term, ctx = Ctx(), meta_ctx=null) {
    switch (term[c]) {
      case "Knd": fail("LHS Infer","Cannot infer the type of Kind !");
      case "Typ": return Knd();
      case "All":
        const dom_sort = this.red.whnf( this.lhs_infer(assumptions, term.dom, ctx) );
        const cod_sort = this.red.whnf( this.lhs_infer(assumptions, term.cod, extend(ctx, [term.name, term.dom])) );
        if (dom_sort[c] != "Typ") {
          fail("LHS Infer","Domain of forall is not a type: `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        if (cod_sort[c] != "Typ" && cod_sort[c] != "Knd") {
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
        const func_t = this.red.whnf(this.lhs_infer(assumptions, term.func, ctx));
        // Technically we don't need to fail here : if we can't infer a product type
        // then we can just ignore the rest of the typing
        // or just check that term.argm is well-typed (with any type).
        // We should probably at least warn that something looks weird though.
        if (func_t[c] !== "All") {
          fail("LHS Infer","Non-function application on `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        this.lhs_check(assumptions, term.argm, func_t.dom, ctx);
        return subst(func_t.cod, term.argm);
      case "Ref": return this.env.do_get(term.name).type;
      case "Var": return get_term(ctx, term.index);
      case "MVar":
        fail("LHS Check", "Could not infer the type of meta-variable instance `"+
          pp_term(term, ctx)+"`.\nThis should not happen... LHS is probably ill-formed (?)");
      default:
        // We could just warn and proceed but this case should only happen in weird cases...
        fail("LHS Infer", "Unable to infer type of `" +
          pp_term(term, ctx) + "`.\n" + pp_context(ctx));
    }
  }
  
  // Checks if a term has given expected type
  lhs_check(assumptions, term, expected_type, ctx = Ctx()) {
    // console.log("LHS Check",term[c],term,pp_term(term,ctx));
    if (term[c] == 'MVar') {
      this.assume_mvar_type(assumptions, term, expected_type, ctx);
    } else {
      const type = this.red.whnf(expected_type);
      if (type[c] === "All" && term[c] === "Lam") {
        if (!term.type.star) { fail("LHS Check", "Please avoid type annotations in LHS..."); }
        this.lhs_infer(assumptions, type, ctx);
        this.lhs_check(assumptions, term.body, type.cod, extend(ctx, [type.name, type.dom]) );
      } else {
        this.assume_convertible(assumptions, type, this.lhs_infer(assumptions, term, ctx));
      }
    }
  }
  
  
  //////////////////////////////////////////////////////////////
  ////////////////////       RHS  Checking  ////////////////////
  //////////////////////////////////////////////////////////////
  
  // Infers the type of a RHS meta-term assuming the given assumptions
  // (that were inferred from typing the LHS)
  rhs_infer(assumptions, term, ctx=Ctx()) {
    // console.log("Infer",term[c],term,pp_term(term,ctx));
    switch (term[c]) {
      case "Knd": fail("RHS Infer","Cannot infer the type of Kind !");
      case "Typ": return Knd();
      case "All":
        const dom_sort = this.red.whnf( this.rhs_infer(assumptions, term.dom, ctx) );
        const cod_sort = this.red.whnf( this.rhs_infer(assumptions, term.cod, extend(ctx, [term.name, term.dom])) );
        if (dom_sort[c] != "Typ") {
          fail("RHS Infer","Domain of forall is not a type: `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx)+ assumptions.pp());
        }
        if (cod_sort[c] != "Typ" && cod_sort[c] != "Knd") {
          fail("RHS Infer","Codomain of forall is neither a type nor a kind: `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx)+ assumptions.pp());
        }
        return cod_sort;
      case "Lam":
        if (term.type === null) {
          fail("Infer","Can't infer non-annotated lambda `" +
            pp_term(term,ctx) + "`.\n" + pp_context(ctx)+ assumptions.pp());
        } else {
          const body_t = this.rhs_infer(assumptions, term.body, extend(ctx, [term.name, term.type]));
          const term_t = All(term.name, term.type, body_t);
          this.rhs_infer(assumptions, term_t, ctx);
          return term_t;
        }
      case "App":
        const func_t = this.whnf(assumptions, this.rhs_infer(assumptions, term.func, ctx));
        if (func_t[c] !== "All") {
          fail("RHS Infer","Non-function application on `" +
            pp_term(term, ctx) + "`.\n" + pp_context(ctx));
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
  rhs_check(assumptions, term, expected_type, ctx=Ctx()) {
    // console.log("CheckWithAssumption",pp_term(term,ctx), pp_term(expected_type,ctx));
    const type = this.whnf(assumptions, expected_type);
    if (type[c] == "All" && term[c] == "Lam") {
      if (!term.type.star && !this.are_convertible(assumptions, term.type, type.dom)) {
        fail("RHS Check", "Incompatible annotation `"+pp_term(term, ctx)+"`."+
          "- Expect = " + pp_term(type.dom, ctx)+"\n"+
          "- Actual = " + pp_term(term.type, ctx)+"\n"+
          pp_context(ctx) + assumptions.pp());
      }
      this.rhs_infer(assumptions, type, ctx);
      this.rhs_check(assumptions, term.body, type.cod, extend(ctx, [type.name, type.dom]));
    } else {
      const term_t = this.rhs_infer(assumptions, term, ctx);
      if (!this.are_convertible(assumptions, type, term_t)) {
        fail("RHS Check", "Type mismatch on `"+pp_term(term, ctx)+"`.\n"+
          "- Expect = " + pp_term(type  , ctx)+"\n"+
          "- Actual = " + pp_term(term_t, ctx)+"\n"+
          pp_context(ctx) + assumptions.pp());
      }
    }
  }
  
  
  //////////////////////////////////////////////////////////////
  ////////////////////       Rule  Checking  ///////////////////
  //////////////////////////////////////////////////////////////
  
  check_rule_well_formed(rule) {
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
    const check_mvar = function(t) {
      if(t[c]==='MVar') {
        if (arities[t.name] && arities[t.name]!==t.args.length) { return true; }
        arities[t.name] = t.args.length;
      }
    }
    const wrong_arity_instance = find_subterm(check_mvar, rule.lhs) || find_subterm(check_mvar, rule.rhs);
    if (wrong_arity_instance) {
      fail("Rule","Meta-vars occurs with several distinct arities `"+
        pp_term(wrong_arity_instance[0],wrong_arity_instance[1]) + "`.");
    }
  }
  
  check_rule_type_preservation(rule) {
    if (!rule.check) { return; }
    const assumptions = new Assumptions(this.sig);
    const inferred_type = this.lhs_infer(assumptions, rule.lhs);
    this.rhs_check(assumptions, rule.rhs, inferred_type);
  }
  
  // Checks type preservation and add a new rule to the reduction machine
  declare_rule(rule) {
    this.check_rule_well_formed(rule);
    this.check_rule_type_preservation(rule);
    this.red.add_new_rule(rule);
  }
  
}
