

function scope_instruction(ins, env) {
  if (ins.term) { ins.term = scope(ins.term, env); }
  if (ins.type) { ins.type = scope(ins.type, env); }
  if (ins.def ) { ins.def  = scope(ins.def , env); }
  if (ins.lhs ) { ins.lhs  = scope(ins.lhs , env); }
  if (ins.rhs ) { ins.rhs  = scope(ins.rhs , env); }
}

// In place scoping of (meta-)term and instructions
function scope(e, env, ctx=Ctx()) {
  if (!e) { return e; }
  switch (e[c]) {
    // Variable, meta-variable or symbol to scope
    case "PreScope":
      const ind = index_of(ctx,e.name);
      if (ind != null) { return Var(ind, preferred_name=e.name); }
      const s = get(env,e.name);
      if (s) { return Ref(s.fullname); }
      return MVar(e.name,[]);
    // (Meta-)term constructors
      break;
    case "PreRef": // Reference to check
      return Ref(do_get(env,e.name).fullname);
    case "All":
      e.dom = scope(e.dom, env, ctx);
      e.cod = scope(e.cod, env, extend(ctx, [e.name,null]));
      break;
    case "Lam":
      e.type = scope(e.type, env, ctx);
      e.body = scope(e.body, env, extend(ctx, [e.name,null]));
      break;
    case "App":
      e.func = scope(e.func, env, ctx);
      e.argm = scope(e.argm, env, ctx);
      break;
    case "MVar":
      for (let i = 0; i < e.args.length; i++) {
        e.args[i] = scope(e.args[i],env,ctx);
      }
      break;
  }
  return e;
}


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

// Checks if two terms are equal
function are_convertible(u, v, red) {
  const acc = [ {a:u,b:v} ];
  while (acc.length > 0) {
    const {a,b} = acc.pop();
    if (equals(a,b)) { continue; }
    if (!same_head( whnf(a,red) , whnf(b,red) ,acc)) { return false; }
  }
  return true;
}

// Substitutes [val] for variable with DeBruijn index [depth]
// and downshifts all variables referencing beyond that index:
// subst(  y#0 \x.(x#0 y#1 z#2) , v#9 )  :=  v#8 \x.(x#0 v#9 z#1)
function subst(term, val, depth=0) {
  switch (term[c]) {
    case "Var":
      return depth === term.index ? val : Var(term.index - (term.index > depth ? 1 : 0));
    case "All":
      const dom = subst(term.dom, val, depth);
      const cod = subst(term.cod, val && shift(val), depth+1);
      return All(term.name, dom, cod);
    case "Lam":
      const type = term.type && subst(term.type, val, depth);
      const body =              subst(term.body, val && shift(val), depth+1);
      return Lam(term.name, type, body);
    case "App":
      const func = subst(term.func, val, depth);
      const argm = subst(term.argm, val, depth);
      return App(func, argm);
    case "MVar":
      const args = term.args.map( (t)=>subst(t,val,depth) );
      return MVar(term.name, args);
    default:
      return term;
  }
}

// Meta-variables substitution
function meta_subst(term, map, depth=0) {
  switch (term[c]) {
    case "All":
      const dom = meta_subst(term.dom, map, depth);
      const cod = meta_subst(term.cod, map, depth+1);
      return All(term.name, dom, cod);
    case "Lam":
      const type = term.type && meta_subst(term.type, map, depth);
      const body =              meta_subst(term.body, map, depth+1);
      return Lam(term.name, type, body);
    case "App":
      const func = meta_subst(term.func, map, depth);
      const argm = meta_subst(term.argm, map, depth);
      return App(func, argm);
    case "MVar":
      const args = term.args.map( (t) => meta_subst(t,map,depth) );
      const s = map[term.name];
      console.log(s);
      if (!s) { return MVar(term.name, args); }
      else { return meta_subst(s, args); }
    default:
      return term;
  }
}


// Infers the type of a term
function infer(term, env, red, ctx = Ctx()) {
  switch (term[c]) {
    case "Knd": throw "Infer:\nCannot infer the type of Kind !";
    case "Typ": return Knd();
    case "All":
      const dom = infer(term.dom, env, red, ctx);
      const cod = infer(term.cod, env, red, extend(ctx, [term.name, term.dom]));
      if (!are_convertible(dom, Typ(), red)) {
        throw "Infer:\nDomain of forall is not a type: `" + pp_term(term, ctx) + "`.\n\n[CONTEXT]\n" + pp_context(ctx);
      }
      if (!are_convertible(cod, Typ(), red) && !are_convertible(cod, Knd(), red)) {
        throw "Infer:\nCodomain of forall is neither a type nor a kind: `" + pp_term(term, ctx) + "`.\n\n[CONTEXT]\n" + pp_context(ctx);
      }
      return cod;
    case "Lam":
      if (term.type === null) {
        throw "Infer:\nCan't infer non-annotated lambda `"+pp_term(term,ctx)+"`.\n\n[CONTEXT]\n" + pp_context(ctx);
      } else {
        const body_t = infer(term.body, env, red, extend(ctx, [term.name, term.type]));
        const term_t = All(term.name, term.type, body_t);
        infer(term_t, env, red, ctx);
        return term_t;
      }
    case "App":
      const func_t = whnf(infer(term.func, env, red, ctx), env, red);
      if (func_t[c] !== "All") {
        throw "Infer:\nNon-function application on `" + pp_term(term, ctx) + "`.\n\n[CONTEXT]\n" + pp_context(ctx);
      }
      const dom_t = subst(func_t.dom, term.argm);
      const argm_v = check(term.argm, dom_t, env, red, ctx, () => "`" + pp_term(term, ctx) + "`'s argument");
      return subst(func_t.cod, argm_v);
    case "Ref":
      return do_get(env,term.name).type;
    case "Var":
      return get_term(ctx, term.index);
    default:
      throw "Infer:\nUnable to infer type of `" + pp_term(term, ctx) + "`.\n\n[CONTEXT]\n" + pp_context(ctx);
  }
}

// Checks if a term has given type
function check(term, type, env, red, ctx = Ctx(), expr) {
  var expr = expr || (() => pp_term(term, ctx));
  var type = whnf(type, env);
  if (type[c] === "All" && term[c] === "Lam" && !term.type) {
    infer(type, env, red, ctx);
    const ex_ctx = extend(ctx, [type.name, type.dom]);
    const body_v = check(term.body, type.cod, env, red, ex_ctx, () => "`" + pp_term(term, ctx) + "`'s body");
    return Lam(type.name, type.dom, body_v);
  } else {
    const term_t = infer(term, env, red, ctx);
    if (!are_convertible(type, term_t, red)) {
      throw "Check:"                     +"\n"+
        "Type mismatch on " + expr()+"." +"\n"+
        "- Expect = " + pp_term(type  , ctx)+"\n"+
        "- Actual = " + pp_term(term_t, ctx)+"\n"+
        "[CONTEXT]"                      +"\n"+
        pp_context(ctx);
    }
    return term;
  }
}

function check_rule_type_preserving(env,rule) {
  // TODO
}

// Checks declared type and adds a new symbol to the environment
function declare_symbol(env, red, ins) {
  const sort = infer(ins.type, env, red);
  if (!are_convertible(sort,Typ(),red) && !are_convertible(sort,Knd(),red)) {
    throw "Declaration:\nDeclared type is not a sort.: `" + pp_term(ins.type) + "`.";
  }
  add_new_symbol(env,ins.name,ins.type);
  log_ok("Symbol declared",ins.name+" with type " +pp_term(ins.type) );
}

// Checks type preservation and add a new rule to the reduction machine
function declare_rule(env,red,rule) {
  check_rule_type_preserving(env,rule);
  add_new_rule(red,rule);
  log_ok("Rewrite rule added",pp_term(rule.lhs)+ " --\> " + pp_term(rule.rhs));
}

// Processes a single instruction
function process_instruction(ins, env, red) {
  scope_instruction(ins, env);
  switch (ins[c]) {
  case "Decl":
    declare_symbol(env, red, ins);
    break;
  case "Def":
    declare_symbol(env, red, ins);
    const rule = Rew(Ref(ins.name),ins.def,ins.name+"_def");
    declare_rule(env, red, rule);
    break;
  case "Rew":
    declare_rule(env, red, ins);
    break;
  case "Req":
    break;
  case "Eval":
    log_info("Eval",pp_term(nf(ins.term, red)));
    break;
  case "Infer":
    log_info("Infer",pp_term(infer(ins.term, env, red)));
    break;
  case "Check":
    check(ins.term, ins.type, env, red);
    log_ok("Check",pp_term(ins.term)+" has indeed type "+pp_term(ins.type));
    break;
  case "Print":
    log_info("Show",pp_term(ins.term));
    break;
  default:
    throw "Instruction:\nUnexepected instruction type:"+ins[c];
  }
}