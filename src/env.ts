type SmbDecl = { fullname:string, proof:boolean; proven:boolean; type:Term };
type EnvMap = Map<string, any>;

class Environment {
  env:EnvMap = new Map();
  // A counter to generate fresh names for anonym meta-variables
  joker_count = 0;
  meta_vars = new Set();
  
  constructor() {}
  
  fresh_name(prefix="*") { return prefix+(this.joker_count++); }
  
  get_namespace(name:string, create_if_not_exists=false) {
    let venv : EnvMap = this.env;
    if (name==="") { return venv;}
    const quals = name.split('.');
    for (let i = 0; i < quals.length; i++) {
      let nvenv = venv.get(quals[i]);
      if (!nvenv) {
        if (!create_if_not_exists) { return undefined; }
        nvenv = new Map();
        venv.set(quals[i], nvenv);
      }
      venv = nvenv;
    }
    return venv;
  }
  
  get(fullname:string, create_if_not_exists=false) {
    let venv = this.env;
    const quals = fullname.split('.');
    const name = quals.pop();
    if (!name) { return undefined; }
    for (let i = 0; i < quals.length; i++) {
      let nvenv = venv.get(quals[i]);
      if (!nvenv) {
        if (!create_if_not_exists) { return undefined; }
        nvenv = new Map()
        venv.set(quals[i], nvenv);
      }
      venv = nvenv;
    }
    if (!venv.get(name) && create_if_not_exists) {
      venv.set(name, {fullname:fullname});
    } else if (create_if_not_exists) {
      fail("Env",`Already defined reference: [${fullname}].`);
    }
    return venv.get(name);
  }
  
  do_get(name:string) {
    const res = this.get(name);
    if (res) { return res; }
    else { fail("Env",`Undefined reference: [${name}].`); };
  }
  
  add_new_symbol(name:string, type:Term, proof=false) {
    const t = this.get(name,true);
    t.type = type;
    if (proof) { t.proof=true; t.proven=false; }
  }
  
  all_proven(namespace:string) {
    const ns = this.get_namespace(namespace);
    if (!ns) { return; }
    ns.forEach(function(smb) {
      if (smb.proof && !smb.proven) {
        fail('Proof',`No proof [${smb.fullname}] was provided for theorem: ${pp_term(smb.type)}`);
      }
    });
  }
  
  scope_instruction(ins:Instruction, namespace='') {
    if (ins.ctx ) { ins.ctx  = this.scope_ctx(      ins.ctx, namespace); }
    if (ins.term) { ins.term = this.scope(ins.term, ins.ctx, namespace); }
    if (ins.type) { ins.type = this.scope(ins.type, ins.ctx, namespace); }
    if (ins.def ) { ins.def  = this.scope(ins.def , ins.ctx, namespace); }
    if (ins.lhs ) { ins.lhs  = this.scope(ins.lhs , ins.ctx, namespace, ins.c==='Rew'); }
    if (ins.rhs ) { ins.rhs  = this.scope(ins.rhs , ins.ctx, namespace); }
    if (namespace) {
      if (ins.name ) { ins.name   = `${namespace}.${ins.name}` ; }
      if (ins.alias) { ins.alias  = `${namespace}.${ins.alias}`; }
    }
  }

  // Scoping of context, potentially in place.
  scope_ctx(ctx:[string, Term][], namespace='') : Ctxt {
    let res = Ctx();
    for (let i = 0; i < ctx.length; i++) {
      res = extend(res, [ ctx[i][0], this.scope(ctx[i][1],res,namespace)]);
    }
    return res;
  }
  // Scoping of (meta-)terms potentially in place.
  scope(term:PreTerm, context=Ctx(), namespace='', lhs=false) : Term {
    const self = this;
    function s(e:PreTerm, ctx:CtxtT<null>) : Term {
      switch (e.c) {
        case "Knd":
        case "Typ":
        case "Var":
        case "Ref": return e;
        case "All": return All(e.name, s(e.dom, ctx), s(e.cod, extend(ctx, [e.name,null])));
        case "Lam": return Lam(e.name, e.type.c === 'Jok' ? e.type : s(e.type, ctx), s(e.body, extend(ctx, [e.name,null])));
        case "App": return App(s(e.func, ctx), s(e.argm, ctx))
        case "MVar": return MVar(e.name, e.args.map((a)=>s(a,ctx)));
        case "Jok": return lhs ? MVar( self.fresh_name() , [...Array( ctx_size(ctx) ).keys()].map((i)=>Var(i))) : e;
        // Variable, meta-variable or symbol to scope
        case "PreScope":
          const ind = index_of(ctx,e.name);
          if (ind != null) { return Var(ind, e.name); }
          const ns = self.get(namespace+(namespace&&".")+e.name);
          return ns ? Ref(ns.fullname) : MVar(e.name,[]);
        // (Meta-)term constructors
        case "PreRef": // Previously defined or loaded reference to locate in the environment
          return Ref(self.do_get(namespace+(namespace&&".")+e.name).fullname);
        default: assertNever(e);
      }
    }
    return s(term, context);
  }

}
