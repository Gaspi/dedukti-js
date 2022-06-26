
class Signature {
  
  constructor(env = new Environment(), red = new ReductionEngine()) {
    this.env = env;
    this.red = red;
    this.rulechecker = new RuleChecker(env,red);
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
      this.infer(type, ctx);
      if (term.type.star) {
        term.type = type.dom;
      } else if (!this.red.are_convertible(term.type, type.dom)) {
        fail("Check", "Incompatible annotation `"+pp_term(term, ctx)+"`."+
          "- Expect = " + pp_term(type.dom, ctx)+"\n"+
          "- Actual = " + pp_term(term.type, ctx)+"\n"+
          pp_context(ctx));
      }
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
  
  // Process a single unscoped instruction
  check_instruction(ins,log=console.log,load=null,namespace="") {
    try {
      this.env.scope_instruction(ins, namespace);
      switch (ins[c]) {
        case "Decl":
          this.declare_symbol(ins);
          log('ok',ins.ln,"Symbol declared",ins.name+" with type " +pp_term(ins.type) );
          break;
        case "DeclConst":
          this.declare_symbol(ins);
          this.red.declare_constant(ins.name);
          log('ok',ins.ln,"Constant symbol declared",ins.name+" with type " +pp_term(ins.type) );
          break;
        case "DeclConstP":
          this.red.declare_constant(ins.name);
          log('ok',ins.ln,"Symbol declared constant",ins.name);
          break;
        case "DeclInj":
          this.red.declare_injective(ins.name);
          log('ok',ins.ln,"Symbol declared injective",ins.name+" (no check)");
          break;
        case "Def":
          this.declare_symbol(ins);
          this.rulechecker.declare_rule( Rew(ins.ln, Ref(ins.name),ins.def,ins.name+"_def") );
          log('ok',ins.ln,"Symbol defined",ins.name+ " as " + pp_term(ins.def));
          break;
        case "Rew":
          this.rulechecker.declare_rule(ins);
          log('ok',ins.ln,"Rewrite rule added",pp_term(ins.lhs)+ " --\> " + pp_term(ins.rhs));
          break;
        case "Eval":
          log('info',ins.ln,"Eval",pp_term(this.red.nf(ins.term, ins.ctx), ins.ctx)+"\n"+pp_context(ins.ctx));
          break;
        case "Infer":
          log('info',ins.ln,"Infer",pp_term(this.infer(ins.term, ins.ctx), ins.ctx)+"\n"+pp_context(ins.ctx));
          break;
        case "CheckType":
          this.check(ins.term, ins.type, ins.ctx);
          log('ok',ins.ln,"CheckType",
            pp_term(ins.term, ins.ctx)+" has indeed type "+pp_term(ins.type, ins.ctx)+"\n"+
            pp_context(ins.ctx));
          break;
        case "CheckConv":
          if (this.red.are_convertible(ins.lhs, ins.rhs)) {
            if (ins.cv) {
              log('ok',ins.ln,"CheckConv",pp_term(ins.lhs,ins.ctx)+" is indeed convertible with "+pp_term(ins.rhs,ins.ctx));
            } else {
              log('warn',ins.ln,"CheckConv",pp_term(ins.lhs,ins.ctx)+" is in fact convertible with "+pp_term(ins.rhs,ins.ctx));
            }
          } else {
            if (ins.cv) {
              log('warn',ins.ln,"CheckConv",pp_term(ins.lhs,ins.ctx)+" is in fact not convertible with "+pp_term(ins.rhs,ins.ctx));
            } else {
              log('ok',ins.ln,"CheckConv",pp_term(ins.lhs,ins.ctx)+" is indeed not convertible with "+pp_term(ins.rhs,ins.ctx));
            }
          }
          break;
        case "Print":
          log('info',ins.ln,'Show',pp_term(ins.term));
          break;
        case "DTree":
          log('info',ins.ln,'DTree',"Decision tree for symbol `"+ins.name+"`:\n"+pp_dtrees(this.red.get(ins.name).decision_trees));
          break;
        case "Req":
          if (!load) { fail('Require',"Current setup does not support `#REQUIRE`."); }
          this.check_instructions(
            load(ins.module),
            (status,ln,title,msg) =>log(status,ins.ln,title,"While loading module `"+ins.module+"`, "+msg),
            load,
            ins.alias ? ins.alias+(namespace&&'.')+namespace : namespace
          );
          break;
        default:
          fail("Instruction","Unexepected instruction constructor:"+ins[c]);
      }
    } catch(e) {
      e.ln = ins.ln;
      throw e;
    }
  }
  
  check_instructions(instructions,log=console.log,load=null,namespace="") {
    if (!Array.isArray(instructions)) {
      fail("Instruction","Unexepected set of instructions. The checker is not used properly...");
    }
    instructions.forEach((ins) => this.check_instruction(ins,log,load,namespace));
  }
}
