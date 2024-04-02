
// A context is a list of [name, type] pairs
type CtxtT<A> = {
  head: [string|null,A];
  tail: CtxtT<A>;
} | null;
type Ctxt = CtxtT<Term>;

// A context is a list of [name, type] pairs
function Ctx():CtxtT<any> { return null; }
function extend<A>(ctx:CtxtT<A>, bind:[string|null,A]):CtxtT<A> { return {head: bind, tail: ctx}; }

function ctx_size(ctx:CtxtT<any>,acc=0):number { return ctx == null ? acc : ctx_size(ctx.tail,acc+1); }

function get_bind(ctx:Ctxt, i:number, j=0) : [string|null, Term|null] | null {
  if (!ctx) {
    return null;
  } else if (j < i) {
    return get_bind(ctx.tail, i, j + 1);
  } else {
    return [ctx.head[0], ctx.head[1] ? shift(ctx.head[1], i+1, 0) : null];
  }
}

function get_name(ctx:Ctxt, i:number, j=0) : string|null {
  if (!ctx) {
    return null;
  } else if (j < i) {
    return get_name(ctx.tail, i, j + 1);
  } else {
    return ctx.head[0];
  }
}

function get_term(ctx:Ctxt, i:number, j=0) {
  if (!ctx) {
    return null;
  } else if (j < i) {
    return get_term(ctx.tail, i, j + 1);
  } else {
    return ctx.head[1] ? shift(ctx.head[1], i+1, 0) : null;
  }
}

function index_of(ctx:CtxtT<any>, name:string, skip=0, i = 0) {
  if (!ctx) {
    return null;
  } else if (ctx.head[0] === name && skip > 0) {
    return index_of(ctx.tail, name, skip-1, i+1);
  } else if (ctx.head[0] !== name) {
    return index_of(ctx.tail, name, skip, i+1);
  } else {
    return i;
  }
}

// DFS searches for a subterm of [term] satisfying the given predicate
function find_subterm(predicate:(t:Term, c:Ctxt)=>boolean, term:Term, ctx:Ctxt=Ctx()) : [Term,Ctxt]|undefined {
  function f(t:Term, c:Ctxt) : undefined {
    if (!t) { return; }
    if (predicate(t, c)) { throw [t,c]; }
    switch (t.c) {
      case "All":
        f(t.dom, c);
        f(t.cod, extend(c, [t.name, t.dom]));
        break;
      case "Lam":
        f(t.type, c);
        f(t.body, extend(c, [t.name, t.type]));
        break;
      case "App":
        f(t.func, c);
        f(t.argm, c);
        break;
      case "MVar":
        t.args.forEach( (subt:Term) => f(subt, c));
        break;
    }
  }
  try { f(term,ctx); }
  catch (e) { return (e as [Term,Ctxt]); }
}

// A term is closed if no subterm can be found that is an out of scope variable.
function is_closed(term:Term):boolean {
  return !find_subterm((t,ctx)=>t.c==='Var'&&t.index>=ctx_size(ctx), term);
}
