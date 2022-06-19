
class Environment {
  env = new Map();
  // A counter to generate fresh names for anonym meta-variables
  star_count = 0;
  meta_vars = new Set();
  
  constructor() {}
  
  fresh_name(prefix="*") { return prefix+(this.star_count++); }
  
  get(fullname, create_if_not_exists=false) {
    let venv = this.env;
    const quals = fullname.split('.');
    const name = quals.pop();
    for (let i = 0; i < quals.length; i++) {
      if (!venv[quals[i]]) {
        if (!create_if_not_exists) { return undefined; }
        venv[quals[i]] = new Map();
      }
      venv = venv[quals[i]];
    }
    if (!venv[name] && create_if_not_exists) {
      venv[name] = {fullname:fullname, rules:[]};
    } else if (create_if_not_exists) {
      fail("Env","Already defined reference: `" + fullname + "`.");
    }
    return venv[name];
  }
  
  do_get(fullname) {
    const res = this.get(fullname);
    if (res) { return res; }
    else { fail("Env","Undefined reference: `" + fullname + "`."); };
  }
  
  add_new_symbol(fullname, type) {
    const t = this.get(fullname,true);
    t.type = type;
  }
  
  scope_instruction(ins) {
    if (ins.ctx ) { ins.ctx  = this.scope_ctx(ins.ctx); }
    if (ins.term) { ins.term = this.scope(ins.term, ins.ctx); }
    if (ins.type) { ins.type = this.scope(ins.type, ins.ctx); }
    if (ins.def ) { ins.def  = this.scope(ins.def , ins.ctx); }
    if (ins.lhs ) { ins.lhs  = this.scope(ins.lhs , ins.ctx); }
    if (ins.rhs ) { ins.rhs  = this.scope(ins.rhs , ins.ctx); }
  }
  
  // Scoping of (meta-)term and instructions, potentially in place.
  scope_ctx(ctx) {
    let res = Ctx();
    for (let i = 0; i < ctx.length; i++) {
      res = extend(res, [ ctx[i][0], this.scope(ctx[i][1],res)]);
    }
    return res;
  }
  // Scoping of (meta-)term and instructions, potentially in place.
  scope(e, ctx=Ctx()) {
    if (!e) { return e; }
    switch (e[c]) {
      // Variable, meta-variable or symbol to scope
      case "PreScope":
        const ind = index_of(ctx,e.name);
        if (ind != null) { return Var(ind, e.name); }
        const s = this.get(e.name);
        if (s) { return Ref(s.fullname); }
        return MVar(e.name,[]);
      // (Meta-)term constructors
        break;
      case "PreRef": // Previously defined or loaded reference to locate in the environment
        return Ref(this.do_get(e.name).fullname);
      case "All":
        e.dom = this.scope(e.dom, ctx);
        e.cod = this.scope(e.cod, extend(ctx, [e.name,null]));
        break;
      case "Lam":
        e.type = this.scope(e.type, ctx);
        e.body = this.scope(e.body, extend(ctx, [e.name,null]));
        break;
      case "App":
        e.func = this.scope(e.func, ctx);
        e.argm = this.scope(e.argm, ctx);
        break;
      case "MVar":
        if (e.star) {
          e.name = this.fresh_name();
          e.args = [...Array( ctx_size(ctx) ).keys()].map(MVar);
          console.log(ctx, ctx_size(ctx), e.args);
        } else {
          for (let i = 0; i < e.args.length; i++) {
            e.args[i] = this.scope(e.args[i],ctx);
          }
        }
        break;
    }
    return e;
  }
  
}
