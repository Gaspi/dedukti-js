

// Pretty prints a context
function pp_context(ctx, i = 0) {
  let res = "";
  while(ctx) {
    res = (ctx.head[0] || '*') + " : " + (ctx.head[1] ? pp_term(ctx.head[1], ctx.tail) : "?") + "\n" + res;
    ctx = ctx.tail;
  }
  return res;
}

// Converts a term to a string
function pp_term_wp(term, ctx = Ctx()) {
  switch (term[c]) {
    case "Knd": return "Kind";
    case "Typ": return "Type";
    case "Var":
      const name = get_name(ctx, term.index)
      return name ? name : "#"+term.index;
    case "App":
    case "All":
    case "Lam": return "("+pp_term(term,ctx)+")";
    case "PreScope": return '?'+term.name;
    case "Ref" : return term.name;
    case "Star": return '*';
    case "MVar": return term.name+"["+term.args.map((x)=>pp_term(x,ctx)).join(',')+"]";
  }
}

function pp_term(term, ctx = Ctx()) {
  switch (term[c]) {
    case "App":
      let text = "";
      while (term[c] === "App") {
        text = pp_term_wp(term.argm,ctx)+" "+text;
        term = term.func;
      }
      return pp_term(term,ctx)+" "+text;
    case "All":
      let dom = pp_term(term.dom,ctx);
      let cod = pp_term(term.cod,extend(ctx, [term.name, null]));
      return (term.name ? "("+term.name+" : "+dom+")" : dom) + " -> "+cod;
    case "Lam":
      let body = pp_term(term.body, extend(ctx, [term.name, null]));
      if (term.type && term.type[c] != 'Star') {
        return "("+term.name+" : "+pp_term(term.type,ctx)+") => "+body;
      } else {
        return term.name + " => "+body;
      }
    case "Knd": case "Typ": case "Var": case "PreScope": case "Ref": case "Star": case "MVar":
      return pp_term_wp(term, ctx);
  }
}