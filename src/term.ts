// A term is an ADT represented by an object in which "c" labels
/*
type Term =
  { c: 'Typ'; }
| { c: 'Knd'; }
| { c: 'Var'; index:number; preferred_name:string|null}
| { c: 'Ref'; name:string}
| { c: 'All'; name:string, dom:Term, cod:Term}
| { c: 'Lam'; name:string, type:Term, body:Term}
| { c: 'App'; func:Term, argm:Term}
| { c: 'MVar'; joker:true}
| { c: 'MVar'; joker:false, name:string|null, args:Term[]};
*/
type Term = {
  readonly c: string;
  [key: string]: any;
}

// A term is an ADT represented by a JSON
function Typ(): Term {
  return { c: 'Typ' };
}
function Knd(): Term {
  return { c: 'Knd' };
}
function Var(index: number, preferred_name: string | null = null): Term {
  return { c: 'Var', index, preferred_name };
}
function Ref(name: string): Term {
  return { c: 'Ref', name };
}
function All(name: string, dom: Term, cod: Term): Term {
  return { c: 'All', name, dom, cod };
}
function Lam(name: string, type: Term, body: Term): Term {
  return { c: 'Lam', name, type, body };
}
function App(func: Term, argm: Term): Term {
  return { c: 'App', func, argm };
}
// Chains applications:  app(a,[b,c,d])  returns  App(App(App(a,b),c),d)
function app(func: Term, args: Term[]) { return args.reduce(App, func); }


// A pattern is a term extended with (potentially anonymous) meta-variables
// A "joker" is an anonym fully applied meta-variable. A default name and the full list of args are assigned at scoping.
function MVar(name: string | null = null, args: Term[] = []): Term { return { c: 'MVar', name, args, joker: false }; }
function Joker(): Term { return { c: 'MVar', joker: true }; }

// Returns the head of a term together with the list of its arguments *in reverse order*
function get_head(t: Term) : [Term, Term[]] {
  const args = [];
  while (t.c == 'App') {
    args.push(t.argm);
    t = t.func;
  }
  return [t, args];
}

// Pre-scoping objects that can be either references or locally bound variables
function PreScope(name: string) { return { c: 'PreScope', name }; }
function PreRef(name: string) { return { c: 'PreRef', name }; }

// Instructions
type Instruction = {
  readonly c: string;
  [key: string]: any;
}
type Rule = { name:string, lhs:Term, rhs:Term };


function Decl(ln: number, name: string, params: [string, Term][], type: Term, def: Term, dtype: string): Instruction {
  return {
    c: 'Decl', ln, name,
    type: type && params.reduceRight((t, [x, ty]) => All(x, ty, t), type),
    def: def ? params.reduceRight((t, [x, ty]) => Lam(x, ty, t), def) : undefined,
    constant: dtype === "cst",
    theorem: dtype === "thm",
  };
}
function Rew(ln:number, lhs: Term, rhs: Term, name: string, check: boolean = true) : Instruction {
  return { c: 'Rew', ln, lhs, rhs, name, check };
}
function DeclInj(ln:number, name: string) : Instruction {
  return { c: 'DeclInj', ln, name };
}
function DeclConst(ln:number, name: string) : Instruction {
  return { c: 'DeclConst', ln, name };
}
function CmdReq(ln:number, module:string, alias:string) : Instruction {
  return { c: 'Req', ln, module, alias };
}
function CmdEval(ln:number, ctx:Term[], term:Term) : Instruction {
  return { c: 'Eval', ln, ctx, term };
}
function CmdInfer(ln:number, ctx:Term[], term:Term) : Instruction {
  return { c: 'Infer', ln, ctx, term };
}
function CmdCheckType(ln:number, ctx:Term[], term:Term, type:Term) : Instruction {
  return { c: 'CheckType', ln, ctx, term, type };
}
function CmdCheckConv(ln:number, ctx:Term[], lhs:Term, rhs:Term, cv:boolean) : Instruction {
  return { c: 'CheckConv', ln, ctx, lhs, rhs, cv };
}
function CmdPrint(ln:number, term:Term) : Instruction {
  return { c: 'Print', ln, term };
}
function CmdDTree(ln:number, name:string) : Instruction {
  return { c: 'DTree', ln, name };
}
function CmdTime(ln:number) : Instruction {
  return { c: 'Time', ln };
}
function CmdDebugOn(ln:number) : Instruction {
  return { c: 'DebugOn', ln };
}
function CmdDebugOff(ln:number) : Instruction {
  return { c: 'DebugOff', ln };
}


// Shifts variables deeper than [depth] by [inc] in the term [term]
function shift(term:Term, inc=1, depth=0):Term {
  switch (term.c) {
    case "Typ": return Typ();
    case "Var":
      return Var(term.index < depth ? term.index : term.index + inc);
    case "Ref":
      return Ref(term.name);
    case "All":
      const dom = shift(term.dom, inc, depth);
      const cod = shift(term.cod, inc, depth + 1);
      return All(term.name, dom, cod);
    case "Lam":
      const type = term.type && shift(term.type, inc, depth);
      const body = shift(term.body, inc, depth + 1);
      return Lam(term.name, type, body);
    case "App":
      return App(shift(term.func, inc, depth), shift(term.argm, inc, depth));
    case "MVar":
      if (term.joker) {
        return term
      } else {
        return MVar(term.name, term.args.map((t:Term) => shift(t, inc, depth)));
      }
    default:
      fail("Shift", `Unexpected constructor: ${term.c}`);
  }
}

// Check that a and b have compatible head. Stacks conversion-relevant subterms in t.
function same_head(a:Term, b:Term, acc:[Term,Term][]) {
  if (a.c !== b.c) { return false; }
  switch (a.c) {
    case "Var": return a.index === b.index;
    case "Ref": return a.name === b.name;
    case "All":
      acc.push([a.dom, b.dom], [a.cod, b.cod]);
      break;
    case "Lam":
      acc.push([a.body, b.body]);
      break;
    case "App":
      acc.push([a.argm, b.argm], [a.func, b.func]);
      break;
    case "MVar":
      if (a.name !== b.name || a.args.length !== b.args.length) { return false; }
      for (let i = 0; i < a.args.length; i++) {
        acc.push([a.args[i], b.args[i]]);
      }
      break;
    case "Typ":
    case "Knd": break;
    default: fail("Equals", `Non matching constructors: ${a.c} / ${b.c}`);
  }
  return true;
}

// Check that a and b have compatible head. Stacks conversion-relevant subterms in t.
function same_head_with_depth(a:Term, b:Term, d:number, acc:[Term,Term,number][]) {
  if (a.c !== b.c) { return false; }
  switch (a.c) {
    case "Var": return a.index == b.index;
    case "Ref": return a.name == b.name;
    case "All":
      acc.push([a.dom, b.dom, d], [a.cod, b.cod, d + 1]);
      break;
    case "Lam":
      acc.push([a.body, b.body, d + 1]);
      break;
    case "App":
      acc.push([a.func, b.func, d], [a.argm, b.argm, d]);
      break;
    case "MVar":
      if (a.name !== b.name || a.args.length !== b.args.length) { return false; }
      for (let i = 0; i < a.args.length; i++) {
        acc.push([a.args[i], b.args[i], d]);
      }
      break;
    case "Typ":
    case "Knd": break;
    default: fail("Equals", `Non matching constructors: ${a.c} / ${b.c}`);
  }
  return true;
}

function equals(u:Term, v:Term) {
  const acc:[Term,Term][] = [[u, v]];
  while (acc.length > 0) {
    const [a, b] = acc.pop() as [Term,Term];
    if (a === b) { continue; }
    if (!same_head(a, b, acc)) { return false; }
  }
  return true;
}

/** Substitutes [val] for variable with DeBruijn index [depth]
 *  and downshifts all variables referencing beyond that index:
 *    subst(  y#0 \x.(x#0 y#1 z#2) , v#9 )  :=  v#8 \x.(x#0 v#9 z#1)
 */
function subst(term:Term, val:Term, depth=0) {
  // Shifts memoisation
  const shifts = [val];
  function s(t:Term, d:number) : Term {
    switch (t.c) {
      case "Var":
        if (t.index != d) {
          return Var(t.index - (t.index > d ? 1 : 0));
        } else {
          if (!shifts[d]) { shifts[d] = shift(val, d); }
          return shifts[d];
        }
      case "All": return All(t.name, s(t.dom, d), s(t.cod, d + 1));
      case "Lam": return Lam(t.name, t.type && s(t.type, d), s(t.body, d + 1));
      case "App": return App(s(t.func, d), s(t.argm, d));
      case "MVar": return MVar(t.name, t.args.map((t:Term) => s(t, d)));
      default: return t;
    }
  }
  return s(term, depth);
}


