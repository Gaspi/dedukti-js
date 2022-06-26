// A context is a list of [name, type] pairs
function Ctx() { return null; }
function extend(ctx, bind) { return {head: bind, tail: ctx}; }

function ctx_size(ctx,acc=0) { return ctx == null ? acc : ctx_size(ctx.tail,acc+1); }

function get_bind(ctx, i, j = 0) {
  if (!ctx) {
    return null;
  } else if (j < i) {
    return get_bind(ctx.tail, i, j + 1);
  } else {
    return [ctx.head[0], ctx.head[1] ? shift(ctx.head[1], i+1, 0) : null];
  }
}

function count(ctx, name, i) {
  return i === 0 ? 0 : (ctx.head[0] === name ? 1 : 0) + count(ctx.tail, name, i-1);
}
function get_name(ctx, i) {
  const bind = get_bind(ctx, i);
  return bind && bind[0];
}

function get_term(ctx, i) {
  const bind = get_bind(ctx, i);
  return bind && bind[1];
}

function index_of(ctx, name, skip=0, i = 0) {
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
