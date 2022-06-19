
// Checks whether the given term a non-pattern meta-variable instance
function is_non_pattern_instance(term) {
  // Only meta-variable can be offending instances
  if (term[c] !== 'MVar') { return false; }
  // We collect the DB index of all arguments that are variables
  const bag = new Set();
  term.args.forEach(a => bag.add(a[c]==="Var" ? a.index : null));
  // The instance is offending if either:
  // - one arguments was not a var (null in the bag)
  // - the number of distincts areguments is less than the number of arguments
  return bag.has(null) || bag.size < term.args.length;
}


// Typing and convertion assumptions mechanisms
class Assumptions {
  constructor(sig) {
    this.sig = sig;
    this.assumed_types = [];
    this.assumed_conv = [];
  }
  
  pp() {
    return "\n[ASSUMPTIONS]\n";
  }
}


// Rule checking entry point
class RuleChecker {
  
  constructor(sig) {
    this.sig = sig;
    this.env = sig.env;
    this.red = sig.red;
  }
  
  // TODO
  add_typing_req(ctx,term,type) {
    if (term[c]!='MVar') { fail('TypingReq', 'Term is not a meta-var: '+pp_term(term,ctx)); }
    if (this.meta_typing_req.get(term.name)) {
      fail('TypingReq', 'Meta-variable '+term.name+' was inferred two typing conditions (most likely non-linear).');
    }
    this.meta_typing_req.set(term.name, [ctx,term,type]);
  }
  
  // TODO
  add_typing_val(term,ctx,val) {
    if (term[c]!='MVar') { fail('TypingVal', 'Term is not a meta-var: '+pp_term(term,ctx)); }
    const prev_val = this.meta_value.get(term.name);
    if (prev_val) {
      if (!are_convertible( meta_subst(prev_val, term.args) ,val)) {
        fail('MVarTyping','Two unconvertible values required for metavar '+term.name);
      }
    } else {
      const msubst = get_meta_match(ctx);
      const mval = meta_match(val, msubst);
      const meta_subst = { [term.name]: mval };
      // TODO
      const typing_req = this.meta_typing_req.get(term.name);
      // Should never happen...
      if (!typing_req) { fail('MVarTyping','No Type inferred for metavar '+term.name); }
      const [ctx,term,type] = typing_req;
      this.check(term,type,ctx);
      this.meta_value.set(term.name, meta_subst);
    }
  }
  
  //////////////////////////////////////////////////////////////
  //////   Typing and convertion assumptions mechanisms  ///////
  //////////////////////////////////////////////////////////////
  
  //TODO: move what is possible to Assumptions...
  
  // Record a new type
  assume_mvar_type(assumptions,term, expected_type, ctx) {
    assumptions.assumed_types.append(
      {
        ctx : ctx,
        name: term.name,
        args: term.args,
        type: expected_type,
      });
  }
  
  
  
  // Note: should return a list of possible types
  get_mvar_type(assumptions, term, ctx) {
    const get_mvar_type_from_assumption = function(assumption) {
      if (assumption.name !== term.name) { return false; }
      
      // Check that the variable substitution S = { assumption.args => term.args (shifted by position in assumption.ctx)  } preserves
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
    }
    return this.assumed_types.find(get_mvar_type_from_assumption);
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
          fail("LHS Infer","Domain of forall is not a type: `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        if (cod_sort[c] != "Typ" && cod_sort[c] != "Knd") {
          fail("LHS Infer","Codomain of forall is neither a type nor a kind: `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        return cod_sort;
      case "Lam":
        if (term.type === null) {
          fail("LHS Infer","Can't infer non-annotated lambda `"+pp_term(term,ctx)+"`.\n" + pp_context(ctx));
        } else {
          const body_t = this.lhs_infer(assumptions, term.body, extend(ctx, [term.name, term.type]));
          const term_t = All(term.name, term.type, body_t);
          this.lhs_infer(assumptions, term_t, ctx);
          return term_t;
        }
      case "App":
        const func_t = this.red.whnf( this.lhs_infer(assumptions, term.func, ctx));
        if (func_t[c] !== "All") {
          fail("LHS Infer","Non-function application on `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        this.lhs_check(assumptions, term.argm, func_t.dom, ctx);
        return subst(func_t.cod, term.argm);
      case "Ref": return this.env.do_get(term.name).type;
      case "Var": return get_term(ctx, term.index);
      case "MVar": fail("LHS Check", "Could not infer the type of meta-variable instance "+pp_term(term, ctx)+". LHS is probably ill-formed.");
      default: fail("LHS Infer","Unable to infer type of `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
    }
  }
  
  // Checks if a term has given expected type
  lhs_check(assumptions, term, expected_type, ctx = Ctx()) {
    // console.log("LHS Check",term[c],term,pp_term(term,ctx));
    if (term[c] == 'MVar') {
      this.assume_mvar_type(assumptions, term, expected_type, ctx);
    } else {
      const type = this.red.whnf(expected_type);
      if (type[c] === "All" && term[c] === "Lam" && !term.type) {
        this.lhs_infer(assumptions, type, ctx);
        this.lhs_check(assumptions, term.body, type.cod, extend(ctx, [type.name, type.dom]) );
      } else {
        const term_t = this.lhs_infer(assumptions, term, ctx);
        if (!this.red.are_convertible(type, term_t)) {
          fail("LHS Check", "Type mismatch on "+pp_term(term, ctx)+"\n"+
            "- Expect = "+pp_term(type  , ctx)+"\n"+
            "- Actual = "+pp_term(term_t, ctx)+"\n"+
            pp_context(ctx));
        }
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
          fail("RHS Infer","Domain of forall is not a type: `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        if (cod_sort[c] != "Typ" && cod_sort[c] != "Knd") {
          fail("RHS Infer","Codomain of forall is neither a type nor a kind: `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        return cod_sort;
      case "Lam":
        if (term.type === null) {
          fail("Infer","Can't infer non-annotated lambda `"+pp_term(term,ctx)+"`.\n" + pp_context(ctx));
        } else {
          const body_t = this.rhs_infer(assumptions, term.body, extend(ctx, [term.name, term.type]));
          const term_t = All(term.name, term.type, body_t);
          this.rhs_infer(assumptions, term_t, ctx);
          return term_t;
        }
      case "App":
        const func_t = this.red.whnf( this.rhs_infer(assumptions, term.func, ctx));
        if (func_t[c] !== "All") {
          fail("RHS Infer","Non-function application on `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        this.rhs_check(assumptions, term.argm, func_t.dom, ctx);
        return subst(func_t.cod, term.argm);
      case "Ref": return this.env.do_get(term.name).type;
      case "Var":
        const ctxt_type = get_term(ctx, term.index);
        if(!ctxt_type) { fail("RHS Infer","Cannot infer the type of free variable "+pp_term(term, ctx)); }
        return ctxt_type;
      case "MVar": return this.get_mvar_type(assumptions, term, ctx);
      default: fail("RHS Infer","Unable to infer type of `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
    }
  }
  
  // Check the type of a RHS meta-term assuming the given assumptions
  // (that were inferred from typing the LHS)
  rhs_check(assumptions, term, expected_type, ctx=Ctx()) {
    // console.log("CheckWithAssumption",rhs[c],rhs, pp_term(rhs,ctx));
    const type = this.red.whnf(expected_type);
    if (type[c] == "All" && term[c] == "Lam" && !term.type) {
      this.rhs_infer(assumptions, type, ctx);
      this.rhs_check(assumptions, term.body, type.cod, extend(ctx, [type.name, type.dom]));
    } else {
      const term_t = this.rhs_infer(assumptions, term, ctx);
      if (!this.red.are_convertible(type, term_t)) {
        fail("RHS Check", "Type mismatch on "+pp_term(term, ctx)+"\n"+
          "- Expect = " + pp_term(type  , ctx)+"\n"+
          "- Actual = " + pp_term(term_t, ctx)+"\n"+
          pp_context(ctx)+
          assumptions.pp());
      }
    }
  }
  
  
  //////////////////////////////////////////////////////////////
  ////////////////////       Rule  Checking  ///////////////////
  //////////////////////////////////////////////////////////////
  
  check_rule_type_preservation(rule) {
    const assumptions = new Assumptions(this.sig);
    const inferred_type = this.lhs_infer(assumptions, rule.lhs);
    this.rhs_check(assumptions, rule.rhs, inferred_type);
  }
  
  // Checks type preservation and add a new rule to the reduction machine
  declare_rule(rule) {
    if (!is_closed(rule.lhs)) { fail("Rule","LHS must be a closed term."); }
    if (!is_closed(rule.rhs)) { fail("Rule","RHS must be a closed term."); }
    // A pattern is ill-formed if a subterm is a non-miller-pattern meta-variable instance
    const illegal_instance = find_subterm(is_non_pattern_instance, rule.lhs);
    if (illegal_instance) {
      fail("Rule","Meta-vars in LHS must be applied to distinct variables: "+
        pp_term(illegal_instance[0],illegal_instance[1]));
    }
    if (rule.check) { this.check_rule_type_preservation(rule); }
    this.red.add_new_rule(rule);
  }
  
}
