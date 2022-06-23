

// DFS searches for a subterm of [term] satisfying the given predicate
function find_subterm(predicate, term, ctx=Ctx()) {
  if (!term) { return undefined; }
  const here = predicate(term, ctx);
  if (here) { return [term,ctx]; }
  switch (term[c]) {
    case "All":
      return find_subterm(predicate, term.dom, ctx) ||
             find_subterm(predicate, term.cod, extend(ctx, [term.name, term.dom]));
    case "Lam":
      return find_subterm(predicate, term.type, ctx) ||
             find_subterm(predicate, term.body, extend(ctx, [term.name, term.type]));
    case "App":
      return find_subterm(predicate, term.func, ctx) ||
             find_subterm(predicate, term.argm, ctx);
    case "MVar":
      return term.args.find(t=>find_subterm(predicate, t, ctx));
    default: return undefined;
  }
}

// A term is closed if no subterm can be found that is an out of scope variable.
function is_closed(term) {
  return !find_subterm((t,ctx)=>t[c]==='Var'&&t.index>=ctx_size(ctx), term);
}

class Signature {
  constructor(env = new Environment(), red = new ReductionEngine()) {
    this.env = env;
    this.red = red;
  }
  
  // Infers the type of a term
  infer(term, ctx=Ctx()) {
    // console.log("Infer",term[c],term,pp_term(term,ctx));
    switch (term[c]) {
      case "Knd": fail("Infer","Cannot infer the type of Kind !");
      case "Typ": return Knd();
      case "All":
        const dom_sort = this.red.whnf( this.infer(term.dom, ctx) );
        const cod_sort = this.red.whnf( this.infer(term.cod, extend(ctx, [term.name, term.dom])) );
        if (dom_sort[c] != "Typ") {
          fail("Infer","Domain of forall is not a type: `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        if (cod_sort[c] != "Typ" && cod_sort[c] != "Knd") {
          fail("Infer","Codomain of forall is neither a type nor a kind: `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        return cod_sort;
      case "Lam":
        if (term.type === null) {
          fail("Infer","Can't infer non-annotated lambda `"+pp_term(term,ctx)+"`.\n" + pp_context(ctx));
        } else {
          const body_t = this.infer(term.body, extend(ctx, [term.name, term.type]));
          const term_t = All(term.name, term.type, body_t);
          this.infer(term_t, ctx);
          return term_t;
        }
      case "App":
        const func_t = this.red.whnf( this.infer(term.func, ctx));
        if (func_t[c] !== "All") {
          fail("Infer","Non-function application on `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
        }
        this.check(term.argm, func_t.dom, ctx);
        return subst(func_t.cod, term.argm);
      case "Ref": return this.env.do_get(term.name).type;
      case "Var":
        const ctxt_type = get_term(ctx, term.index);
        if(!ctxt_type) { fail("Infer","Cannot infer the type of free variable "+pp_term(term, ctx)); }
        return ctxt_type;
      case "MVar": fail("Infer","Cannot infer the type of a meta-variable instance: "+pp_term(term, ctx));
      default: fail("Infer","Unable to infer type of `" + pp_term(term, ctx) + "`.\n" + pp_context(ctx));
    }
  }
  
  // Checks if a term has given expected type
  check(term, expected_type, ctx=Ctx()) {
    // console.log("Check",term[c],term, pp_term(term,ctx));
    if (term[c] == 'MVar') { fail("Check", "Cannot check the type of a meta-variable instance: "+pp_term(term, ctx)); }
    const type = this.red.whnf(expected_type);
    if (type[c] == "All" && term[c] == "Lam") {
      if (!term.type.star && !this.red.are_convertible(term.type, type.dom)) {
        fail("Check", "Incompatible annotation `"+pp_term(term, ctx)+"`."+
          "- Expect = " + pp_term(type.dom, ctx)+"\n"+
          "- Actual = " + pp_term(term.type, ctx)+"\n"+
          pp_context(ctx));
      }
      this.infer(type, ctx);
      this.check(term.body, type.cod, extend(ctx, [type.name, type.dom]));
    } else {
      const term_t = this.infer(term, ctx);
      if (!this.red.are_convertible(type, term_t)) {
        fail("Check", "Type mismatch on "+pp_term(term, ctx)+"\n"+
          "- Expect = " + pp_term(type  , ctx)+"\n"+
          "- Actual = " + pp_term(term_t, ctx)+"\n"+
          pp_context(ctx));
      }
    }
  }
  
  // Checks declared type and adds a new symbol to the environment
  declare_symbol(ins) {
    const sort = this.red.whnf( this.infer(ins.type) );
    if (sort[c] != "Typ" && sort[c] != "Knd") {
      fail("Declaration","Declared type is not a sort.: `" + pp_term(ins.type) + "`.");
    }
    this.env.add_new_symbol(ins.name,ins.type);
  }
  
  is_injective(term) {
    return term[c] === 'Var' ||
      (term[c] === 'MVar' && false) // TODO implement injective symbols
  }
}
