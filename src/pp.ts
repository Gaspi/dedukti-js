
// Converts a term to a string
function pp_term_wp(term:Term, ctx=Ctx()) : string {
  switch (term.c) {
    case "Knd": return "Kind";
    case "Typ": return "Type";
    case "Var": return get_name(ctx, term.index) || "#"+term.index;
    case "App":
    case "All":
    case "Lam": return "("+pp_term(term,ctx)+")";
    case "Ref" : return term.name;
    case "Jok" : return '*';
    case "MVar": return term.name+"["+term.args.map((x:Term)=>pp_term(x,ctx)).join(',')+"]";
    default: assertNever(term);
  }
}

function pp_term(term:Term, ctx = Ctx()) : string {
  switch (term.c) {
    case "App":
      let text = "";
      for(; term.c === "App"; term = term.func) {
        text = pp_term_wp(term.argm,ctx)+" "+text;
      }
      return pp_term(term,ctx)+" "+text;
    case "All":
      let dom = (term.name ? "("+term.name+" : "+pp_term(term.dom,ctx)+")" : pp_term_wp(term.dom,ctx));
      let cod = pp_term(term.cod,extend(ctx, [term.name, Joker()]));
      return dom+" -> "+cod;
    case "Lam":
      let body = pp_term(term.body, extend(ctx, [term.name, Joker()]));
      return "(" + (term.type ? "("+term.name+" : "+pp_term(term.type,ctx)+")" : term.name) + " => "+body+")";
    case "Knd": case "Typ": case "Var": case "Ref": case "MVar": case "Jok":
      return pp_term_wp(term, ctx);
    default: assertNever(term);
  }
}

// Pretty prints a context
function pp_context(ctx:Ctxt, i=0) {
  let res = "";
  while(ctx) {
    res = (ctx.head[0] || '*') + " : " + (ctx.head[1] ? pp_term(ctx.head[1], ctx.tail) : "?") + "\n" + res;
    ctx = ctx.tail;
  }
  return "\n[CONTEXT]\n"+res;
}
