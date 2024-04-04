// A term is an ADT represented by an object in which "c" labels the type

type TermVar =
  { c: 'Var', index:number, preferred_name:string|null};
type TermMVar =
  { c: 'MVar', name:string|number|null, args:Term[] };
type TermNoApp =
  { c: 'Knd' }
| { c: 'Typ' }
| { c: 'All', name:string|null, dom:Term, cod:Term}
| { c: 'Lam', name:string, type:Term, body:Term}
| TermVar
| { c: 'Ref', name:string}
| TermMVar
| { c: 'Jok' };
// A Joker means different things depending on the context:
// - In a LHS : it is an unnamed fully applied meta-var that doesn't occur on the RHS. [target] is an expected type
// - In a term : it is an unknown term that is meant to be inferred (and repalced in place) at typechecking.

type GeneralTerm<T> =
  { c: 'Knd' }
| { c: 'Typ' }
| { c: 'All', name:string|null, dom:GeneralTerm<T>, cod:GeneralTerm<T>}
| { c: 'Lam', name:string, type:GeneralTerm<T>, body:GeneralTerm<T>}
| { c: 'Var', index:number, preferred_name:string|null}
| { c: 'Ref', name:string}
| { c: 'MVar', name:string|number|null, args:GeneralTerm<T>[] }
| { c: 'Jok' }
| { c: 'App', func:GeneralTerm<T>, argm:GeneralTerm<T>}
| T;
type Term = GeneralTerm<never>;

type PreConst =
  { c: 'PreRef'; name:string}
| { c: 'PreScope'; name:string};

type PreTerm = GeneralTerm<PreConst>;

type PureTerm =
  { c: 'Knd' }
| { c: 'Typ' }
| { c: 'All', name:string|null, dom:PureTerm, cod:PureTerm}
| { c: 'Var', index:number, preferred_name:string|null}
| { c: 'Ref', name:string}
| { c: 'Lam', name:string, type:PureTerm, body:PureTerm}
| { c: 'App', func:PureTerm, argm:PureTerm};


// A term is an ADT represented by a JSON
function Typ(): GeneralTerm<any> {
  return { c: 'Typ' };
}
function Knd(): GeneralTerm<any> {
  return { c: 'Knd' };
}
function Var(index: number, preferred_name: string | null = null): GeneralTerm<any> {
  return { c: 'Var', index, preferred_name };
}
function Ref(name: string): GeneralTerm<any> {
  return { c: 'Ref', name };
}
function All<T>(name: string|null, dom: GeneralTerm<T>, cod: GeneralTerm<T>): GeneralTerm<T> {
  return { c: 'All', name, dom, cod };
}
function Lam<T>(name: string, type: GeneralTerm<T>, body: GeneralTerm<T>): GeneralTerm<T> {
  return { c: 'Lam', name, type, body };
}
function App<T>(func: GeneralTerm<T>, argm: GeneralTerm<T>): GeneralTerm<T> {
  return { c: 'App', func, argm };
}
// Chains applications:  app(a,[b,c,d])  returns  App(App(App(a,b),c),d)
function app<T>(func: GeneralTerm<T>, args: GeneralTerm<T>[]) : GeneralTerm<T> {
  return args.reduce(App, func);
}

// A pattern is a term extended with (potentially anonymous) meta-variables
// A "joker" is an anonym fully applied meta-variable. A default name and the full list of args are assigned at scoping.
function MVar<T>(name: string | number | null = null, args: GeneralTerm<T>[] = []): GeneralTerm<T> {
  return { c: 'MVar', name, args };
}
function Joker(): GeneralTerm<any> { return { c: 'Jok' }; }

// Pre-scoping objects that can be either references or locally bound variables
function PreScope(name: string) : PreTerm { return { c: 'PreScope', name }; }
function PreRef(name: string) : PreTerm { return { c: 'PreRef', name }; }

// Returns the head of a term together with the list of its arguments *in reverse order*
function get_head(t: Term) : [TermNoApp, Term[]] {
  const args = [];
  while (t.c === 'App') {
    args.push(t.argm);
    t = t.func;
  }
  return [t, args];
}

// Instructions
type Instruction = {
  readonly c: string;
  readonly ln: number;
  [key: string]: any;
}

type Rule = Instruction & { name:string, lhs:Term, rhs:Term, check:boolean };


function Decl(ln: number, name: string, params: [string, Term][], type: Term|null, def ?: Term|null, dtype?: string): Instruction {
  return {
    c: 'Decl', ln, name,
    type: type && params.reduceRight((t, [x, ty]) => All(x, ty, t), type),
    def: def ? params.reduceRight((t, [x, ty]) => Lam(x, ty, t), def) : undefined,
    constant: dtype === "cst",
    theorem: dtype === "thm",
  };
}

function Rew(ln:number, lhs: Term, rhs: Term, name: string, check: boolean = true) : Rule {
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
    case "Knd":
    case "Typ":
    case "Jok": return term;
    case "Var":
      return Var(term.index < depth ? term.index : term.index + inc);
    case "Ref":
      return Ref(term.name);
    case "All":
      return All(term.name,
        shift(term.dom, inc, depth),
        shift(term.cod, inc, depth + 1));
    case "Lam":
      return Lam(term.name, 
        term.type && shift(term.type, inc, depth),
        shift(term.body, inc, depth + 1));
    case "App":
      return App(shift(term.func, inc, depth), shift(term.argm, inc, depth));
    case "MVar":
      return MVar(term.name, term.args.map((t:Term) => shift(t, inc, depth)));
    default: assertNever(term);
  }
}

// Check that a and b have compatible head. Stacks conversion-relevant subterms in t.
function same_head(a:Term, b:Term, acc:[Term,Term][]) {
  if (a.c !== b.c) { return false; }
  switch (a.c) {
    case "Typ":
    case "Knd": 
    case "Jok": break;
    case "Var": return a.index === (b as typeof a).index;
    case "Ref": return a.name === (b as typeof a).name;
    case "All":
      acc.push([a.dom, (b as typeof a).dom], [a.cod, (b as typeof a).cod]);
      break;
    case "Lam":
      acc.push([a.body, (b as typeof a).body]);
      break;
    case "App":
      acc.push([a.argm, (b as typeof a).argm], [a.func, (b as typeof a).func]);
      break;
    case "MVar":
      if (a.name !== (b as typeof a).name || a.args.length !== (b as typeof a).args.length) { return false; }
      for (let i = 0; i < a.args.length; i++) {
        acc.push([a.args[i], (b as typeof a).args[i]]);
      }
      break;
    default: assertNever(a);
  }
  return true;
}

// Check that a and b have compatible head. Stacks conversion-relevant subterms in t.
function same_head_with_depth(a:Term, b:Term, d:number, acc:[Term,Term,number][]) {
  if (a.c !== b.c) { return false; }
  switch (a.c) {
    case "Typ":
    case "Knd": 
    case "Jok": break;
    case "Var": return a.index == (b as typeof a).index;
    case "Ref": return a.name == (b as typeof a).name;
    case "All":
      acc.push([a.dom, (b as typeof a).dom, d], [a.cod, (b as typeof a).cod, d + 1]);
      break;
    case "Lam":
      acc.push([a.body, (b as typeof a).body, d + 1]);
      break;
    case "App":
      acc.push([a.func, (b as typeof a).func, d], [a.argm, (b as typeof a).argm, d]);
      break;
    case "MVar":
      if (a.name !== (b as typeof a).name || a.args.length !== (b as typeof a).args.length) { return false; }
      for (let i = 0; i < a.args.length; i++) {
        acc.push([a.args[i], (b as typeof a).args[i], d]);
      }
      break;
    default: assertNever(a);
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


