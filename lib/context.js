// A context is a list of [name, type] pairs
function Ctx() { return null; }
function extend(ctx, bind) { return {head: bind, tail: ctx}; }

function get_bind(ctx, i, j = 0) {
  if (!ctx) {
    return null;
  } else if (j < i) {
    return get_bind(ctx.tail, i, j + 1);
  } else {
    return [ctx.head[0], ctx.head[1] ? shift(ctx.head[1], i, 0) : null];
  }
}

function count(ctx, name, i) {
  return i === 0 ? 0 : (ctx.head[0] === name ? 1 : 0) + count(ctx.tail, name, i-1);
}
function get_name(ctx, i) {
  const bind = get_bind(ctx, i);
  return (bind?bind[0]:'')+"#"+i;
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