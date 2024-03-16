
function filter_rules(rules,arity) {
  const res = [];
  let max = -1;
  for (let i = 0; i < rules.length; i++) {
    const ar = rules[i].stack.length;
    if (ar > arity) { continue; }
    res.push(rules[i]);
    if (ar > max) { max = ar; }
  }
  return [ res , max ];
}

// Note : meta-substitution are done "by name" > avoid capture !
//     f X[] Y[] { X => t, Y => u } --> f t u
// meta-variable instantiation is done "by DB index"
//     X[t,u] { X[x,y] => f x y } --> f x[0] y[1] { [0] => t, [1] => u }


/** A term representation for faster computation:
    - provides easy access to its "head"
    - can be reduced in place
    - built-in memoization of back (shifted) translations to actual (reduced) terms
    [head] is a term and should not be modified in place, only inspected
    [ctxt] is possibly shared among states and must not be modified in place
    [stack] may be modified in place
 */
class State {
  constructor(term, ctxt=new Context(), stack=[]) {
    this.head = term;
    // The stack is meant to be modified in place
    this.stack = stack;
    this.ctxt = ctxt;
    // The head and context are likey shared among states and must not be modified in place
    // Array of shifted term representations of the state. Should be reset every time the state is updated
    this._terms = [];
    this._heads = [];
    if (ctxt.isEmpty() && !stack.length) {
      // If the state is created without context or stack, it is cast back by default to the same term
      this._terms = [ term ];
    }
    this._head = this.head;
    this._ctxt = this.ctxt;
    this._shifted = [this];
  }

  getShifted(s) {
    if (!this._shifted[s]) {
      this._shifted[s] = new ShiftedState(this, s);
    }
    return this._shifted[s];
  }
  getState() { return this; }
  getShift() { return 0; }

  pp() {
    return pp_term(this.head) + (this.stack.length ? " with " + this.stack.length + " args" : "") + this.ctxt.pp();
  }

  getHeadC() {
    return this.head.c;
  }


  getHeadName() {
    return this.head.name;
  }

  getHeadIndex() {
    return this.head.index;
  }

  getHeadDom() {
    return new State(this.head.dom, this.ctxt);
  }

  getHeadType() {
    return new State(this.head.type, this.ctxt);
  }

  getHeadArgs() {
    const ctxt = this.ctxt;
    return this.head.args.map( (a)=>new State(a, ctxt) );
  }

  getHeadBody() {
    return new State(this.head.body, this.ctxt.shift_extend());
  }

  getHeadCod() {
    return new State(this.head.cod, this.ctxt.shift_extend());
  }

  nbArgs() {
    return this.stack.length;
  }

  forEachArg(f) {
    this.stack.forEach(f);
  }

  // Term conversion with memoisation of shifted versions of head and global terms to avoid recomputing and have maximum sharing
  _to_term(s=0) {
    // Memoisation of head shifted versions
    if (!this._heads[s]) {
      if (!this._heads[0]) {
        this._heads[0] = this.ctxt.apply(this.head);
      }
      this._heads[s] = shift(this._heads[0], s);
    }
    return this.stack.map( (e)=>e.to_term(s) ).reduceRight(App, this._heads[s] );
  }

  check_memoization() {
    if (this._head === this.head && this._ctxt === this.ctxt) { return; }
    this._terms = [];
    this._heads = [];
    this._head = this.head;
    this._ctxt = this.ctxt;
  }

  // Memoised version
  // TODO: detect closed terms (unchanged by shifting) and avoid computing their shifted versions at all
  to_term(s=0) {
    this.check_memoization();
    if (!this._terms[s]) {
      this._terms[s] = this._to_term(s);
    }
    return this._terms[s];
  }

  compress() {}

  // Substitute the head of this state to a an other state
  link_to(state) {
    if (!this.stack.length) {
      delete this.head;
      delete this.stack;
      delete this.ctxt;
      delete this._terms;
      delete this._heads;
      delete this._head;
      delete this._ctxt;
      this.state = state;
      this.shift = 0;
      this.__proto__ = ShiftedState.prototype;
      this.compress();
      this._shifted.forEach(function(e) { e.state = state; });
      delete this._shifted;
    } else if (state instanceof State) {
      this.head = state.head;
      this.ctxt = state.ctxt;
      this.stack = this.stack.concat(state.stack);
    } else {
      this.head = state.to_term();
      this.ctxt = new Context();
    }
  }
}

class ShiftedState {
  constructor(state, shift=1) {
    this.state = state;
    this.shift = shift;
    this.compress();
  }

  getShifted(s) { return this.state.getShifted(this.shift+s); }
  getState() { return this.state; }
  getShift() { return this.shift; }

  pp() {
    if (this.state === null) {
      return "[X]";
    } else {
      return "[+"+this.shift+"] "+this.state.pp();
    }
  }

  // Graph compression
  compress() {
    if (this.state instanceof ShiftedState) {
      // TODO : check if this is ever executed
      this.shift = this.state.shift + this.shift;
      this.state = this.state.state;
    }
  }

  // Overriding term conversion
  to_term(s=0) {
    return this.state.to_term(s+this.shift);
  }

  getHeadC() {
    return this.state.getHeadC();
  }

  getHeadName() {
    return this.state.getHeadName();
  }

  getHeadIndex() {
    return this.state.getHeadIndex()+this.shift;
  }

  getHeadBody() {
    if (!this.state.getHeadBody()) {
      throw("debug");
    }
    return new ShiftedState(this.state.getHeadBody(), this.shift);
  }

  nbArgs() {
    return this.state.nbArgs();
  }

  forEachArg(f) {
    this.state.forEachArg( (a)=> f(new ShiftedState(a, this.shift)));
  }
}

function check_meta_match(term, map) {
  const depth = map.length;
  if (depth == 0) { return true; }
  function chk(t,d) {
    switch (t.c) {
      case "Var" :
        if (t.index >= d && t.index < d + depth && map[t.index - d] === undefined) {
          fail('MetaMatchFailed',"Unexpected locally bound variable ["+pp_term(t)+"]." );
        }
        break;
      case "All" :
        chk(t.dom,d);
        chk(t.cod,d+1);
        break;
      case "Lam" :
        if (t.type) {
          chk(t.type,d)
        }
        chk(t.body,d+1);
        break;
      case "App" :
        chk(t.func,d);
        chk(t.argm,d);
        break;
      case "MVar":
        t.args.forEach( (t)=>chk(t,d) );
        break;
    }
  }
  return chk(term,0);
}

/** General class to represent a match from a LHS
 */
class ComplexMatch {
  constructor(term, map) {
    check_meta_match(term, map);
    this.term = term;
    this.map = map;
  }
  meta_apply(args) {
    const subst = this.map.map( (i) => (i === undefined ? undefined : args[i]) );
    const ctxt = new Context(new Map(), 0, subst);
    return new State(this.term, ctxt);
  }
}

/** Substitute the states in the array [args]
  for the first non-already-substituted bound variables in state [s]
*/
function meta_appply_subst(args, s) {
  const state = s.getState();
  // Create a new context based on the provided arguments substituted in
  // [ s1, Shifted(null, 0), Shifted(null, 1), Shifted(s2,2), Shifted(null, 2), Shifted(null, 3), Shifted(s3,4) ]  <- [a,b,c]
  // [ s1, a, b, s2, c, Shifted(null, 0), Shifted(s3,1) ]
  let arg_i = 0;
  const new_subst = state.ctxt.subst.map( function (e,i) {
    const nshift = e.getShift() - arg_i;
    if (arg_i < args.length && e.getState() === null) {
      e = args[arg_i++];
    }
    return e.getShifted(nshift);
  });
  // assert arg_i == args.length
  const new_ctxt = new Context(state.ctxt.meta, state.ctxt.depth - args.length, new_subst);
  return_state = new State(state.head, new_ctxt, state.stack.map((e)=> meta_appply_subst(args,e)));
  return return_state.getShifted(s.getShift());
}

/** Class for specific match X[x,y,...] where x,y,... are all locally bound variables in their DB order
    In that case, no need we record the state
 */
class SimpleMatch {
  constructor(state) {
    this.state = state;
  }

  meta_apply(args) {
    if (args.every( (e,i) => e.c === 'Var' && e.index === i )) {
      return this.state;
    } else {
      return meta_appply_subst(args, this.state);
    }
  }
}


// A context is a mapping of some meta-variables and variables in a term
// to states (which can be computed to term if needed).
// Meta-variables are mapped to "matches" (SimpleMatch / ComplexMatch) which are meat_applied to states
// It can be applied to terms.
class Context {
  constructor(meta=new Map(), depth=0, subst=[]) {
    this.meta = meta;
    this.depth = depth;
    // Depth of the meta substitution
    // Should be equal to the number of null in subst
    this.subst = subst;
    // Array of states substituable to meta-variables
  }

  isEmpty() {
    return this.meta.size == 0 && this.depth == 0 && this.subst.length == 0;
  }

  pp() {
    return (this.meta.size == 0 ? "" : " [Meta: " + this.meta.size + " under " + this.depth             + "]") +
        (this.subst.length == 0 ? "" : " [Vars: " + this.subst.map( (e,i) => i+"->"+ (e === null ? 'itself' : e.pp())).join(' , ') + "]");
  }

  substVar(db) {
    const st = this.subst[db];
    if (st === undefined) {
      // This should not happen !
      // Most likely a HO meta-var was wrongly substituted
      throw new Error("[ContextSubst] This should not happen !");
    }
    return st;
  }

  extend(s) {
    return new Context( this.meta, this.depth, [s].concat( this.subst ) );
  }

  shift_extend() {
    return new Context( this.meta, this.depth+1, [new ShiftedState(null,0)].concat(this.subst.map((s) => new ShiftedState(s,1))) );
  }

  shift_extend_d(d) {
    const new_subst = new Array(d+this.subst.length);
    for (let i = 0; i < d; i++) {
      new_subst[i] = new ShiftedState(null,i);
    }
    for (let i = d; i < d+this.subst.length; i++) {
      new_subst[i+d] = new ShiftedState( this.subst[i], d);
    }
    return new Context(this.meta, this.depth+d, new_subst);
  }

  apply(term, depth=0) {
    const self = this;
    const varshift = this.subst.length - this.depth;
    // Compteur de substitutions
    let ct = 0;
    function e(t,d) {
      const cta = ct;
      if (t.c == "MVar") {
        const meta_state = self.meta.get(t.name);
        if (!meta_state) {
          const args = t.args.map( (t)=>e(t,d) );
          return (ct === cta ? t : MVar(t.name, args));
        } else {
          ct += 1; // Meta-substitution effectuée
          const state_args = t.args.map( (t)=>new State(t,self.shift_extend_d(d)) );
          return meta_state.meta_apply(state_args).to_term(d+self.depth);
        }
      } else if (t.c === "Var") {
        const db = t.index - d;
        if (db < 0) { // Locally bound variable
          return t;
        } else if (db >= self.subst.length) { // Free variable from outside the context
          if (varshift == 0) {
            return t;
          } else {
            ct += 1; // Variable shifting occurs
            return Var(t.index - varshift);
          }
        } else {
          const st = self.substVar(db);
          if (st.state === null) { // The variable is free in the context
            if (db == st.shift) {
              return t; //
            } else {
              ct += 1; // Variable shifting occurs
              return Var(t.index - db + st.shift);
            }
          } else {
            ct += 1; // Variable substitution occurs
            return st.to_term(d);
          }
        }
      } else if (t.c === "All") {
        const dom = e(t.dom, d  );
        const cod = e(t.cod, d+1);
        return (ct === cta) ? t : All(t.name, dom, cod);
      } else if (t.c === "Lam") {
        const type = t.type && e(t.type, d  );
        const body =           e(t.body, d+1);
        return (ct === cta) ? t : Lam(t.name,type,body);
      } else if (t.c === "App") {
        const func = e(t.func,d);
        const argm = e(t.argm,d);
        return (ct === cta) ? t : App(func,argm);
      } else {
        return t;
      }
    }
    return e(term, depth);
  }
}


class ReductionEngine {
  constructor() {
    this.red = new Map();
  }

  // Get info about a symbol (adds a new entry if needed)
  get(name) {
    if (!this.red.has(name)) {
      this.red.set(name, { rules:[], decision_trees:[], injective:false });
    }
    return this.red.get(name);
  }

  add_new_rule(rule) {
    // Find the head symbol and the stack of the rule
    const [head,stack] = get_head(rule.lhs);
    if (head.c !== 'Ref') {
      fail("Scope","Unexpected head symbol in rule left-hand side: "+head.c);
    }
    rule.head = head.name;
    rule.stack = stack;
    const smb = this.get(head.name);
    if (smb.injective) {
      fail("RuleAdd","The injective symbol `"+head.name+"` cannot be rewritten with a new rule.");
    }
    // The new rule is added to the global set of rules for that symbol
    smb.rules.push(rule);
    const dts = smb.decision_trees;
    const arity = stack.length;
    // All DTs of arity greater than that of the new rule are erased
    // (to be recomputed taking into account the new rule)
    for (let i = arity; i < dts.length; i++) { dts[i] = null; }
    // Empty DTs are generated for arities up to that of the new rule
    for (let i = dts.length; i <= arity; i++) { dts.push(null); }
  }

  // Injectivity declaration / checking
  is_injective(name) { return this.get(name).injective; }
  declare_injective(name) { this.get(name).injective=true; }
  declare_constant(name) {
    if (this.get(name).rules.length > 0) {
      fail("ConstantDecl", `The symbol [${name}] is not constant.`);
    }
    this.declare_injective(name);
  }

  // Get the decision tree of given symbol when applied to this many arguments
  get_decision_tree(name,arity) {
    const r = this.red.get(name);
    if (!r || !r.rules.length) { return null; }
    const dts = r.decision_trees;
    if (arity >= dts.length) { arity = dts.length-1; }
    if (!dts[arity]) {
      const [rules, max_arity] = filter_rules(r.rules, arity);
      if (!rules.length) { return null; }
      if (!dts[max_arity]) {
        dts[max_arity] = compute_decision_tree(rules, max_arity);
      }
      if (max_arity < arity) {
        dts[arity] = dts[max_arity];
      }
    }
    return dts[arity];
  }

  // Ideas : add a depth d to states to allow easy lambda deconstruction
  // Add a depth map to states in WHNF : shifting memoisation of terms
  // Ensure term sharing is preserved by non-modifying shifting and (meta-)substitions
  // Use a single function for shifting under depth + subst + meta subst (one pass).
  // Add memoisation of term representation (for sharing) and of whnf state (true/false)
  // Move all this to a class

  // Reduces a term until a normal form is found
  whnf(term) { return this.whnf_state( new State(term) ).to_term(); }
    nf(term) { return   this.nf_state( new State(term) ).to_term();}


  /** Computes the strong normal form of a state
  */
  nf_state(state) {
    //console.log("NF: "+state.pp(), state);
    this.whnf_state(state);
    //console.log("[NF] Computing WHNF of "+state.pp());
    const s = state instanceof ShiftedState ? state.state : state;
    //console.log("[NF] Computed WHNF: "+pp_term(s.to_term()));
    for (let i=0; i < s.stack.length; i++) { s.stack[i] = this.nf_state(s.stack[i]); };
    switch (s.head.c) {
      case "All":
        s.head = All(
          s.head.name,
          this.nf_state( s.getHeadDom() ).to_term(),
          this.nf_state( s.getHeadCod() ).to_term());
        break;
      case "Lam":
        s.head = Lam(
          s.head.name,
          this.nf_state( s.getHeadType() ).to_term(),
          this.nf_state( s.getHeadBody() ).to_term());
        break;
      case "MVar":
        s.head = MVar(s.head.name,
          s.getHeadArgs().map( (e)=> this.nf_state(e).to_term()));
        break;
      case "App":
        throw("This should not happen");
        break;
    }
    state.compress();
    return state;
  }

  /** Computes the weak head normal form of term given in state representation: [head,stack,subst,meta_subst]
    * Updates the [state] Array in place
    * [subst] and [meta_subst] may be shared among states and must not be modified in place
    * [head] is a term and should not be modified, only deconstructed
    * [stack] can be modified in place, it is never shared
    */
  whnf_state(state) {
    while (true) {
      //console.log("WHNF:", state.pp(), state);
      if (state instanceof ShiftedState) {
        this.whnf_state(state.state);
        state.compress();
        return state;
      }
      while (state.head.c === "App") {
        // Push the state version of the argument on the stack
        state.stack.push( new State(state.head.argm, state.ctxt) );
        state.head = state.head.func;
      }
      // Replace switch with if (local variables are declared)
      switch (state.head.c) {
        case "Lam":
          // Unapplied lambda is a WHNF
          if (state.stack.length === 0) { return state; }
          // Otherwise add the top stack argument to the substitution
          // and compute the WHNF of the body (\x.t) u1 u2 ... --> t[x\u1] u2 ...
          state.head = state.head.body;
          state.ctxt = state.ctxt.extend( state.stack.pop() );
          break;
        case "Ref": // Potential redex
          const rule_name = this.head_rewrite(state);
          // If rewriting occured, proceed with current state, otherwise return
          if (!rule_name) { return state; }
          break;
        case "MVar":
          const meta_state = state.ctxt.meta.get( state.head.name );
          if (!meta_state) { return state; }
          const meta_subst_state = meta_state.meta_apply(state.getHeadArgs());
          state.link_to(meta_subst_state);
          break;
        case "Var":
          if (state.head.index >= state.ctxt.subst.length) {
            return state;
          }
          const subst_state = state.ctxt.substVar(state.head.index);
          if (subst_state.state === null) {
            return state;
          } else {
            state.link_to(subst_state);
          }
          break;
        default: return state; // Any other construction
      }
    }
  }

  // Applies a (single) rewrite step at the head if any rule matches at the head
  // Updates [state] in place and returns the name of the rule used or null if no step was performed
  // asserts: state instanceof State
  head_rewrite(state) {
    // Getting the head symbol's decision tree
    const dtree = this.get_decision_tree(state.head.name, state.stack.length);
    if (!dtree) { return null; }
    // Truncate to keep only the first [arity] arguments from the top of the stack
    const truncated_stack = state.stack.slice(state.stack.length-dtree.arity);
    // Running the decision tree with the given args (in order)
    let [rule, meta_subst] = this.exec_dtree(dtree.tree,truncated_stack);
    if (!rule) { return null; }
    state.head = rule.rhs;
    state.stack = state.stack.slice(0,state.stack.length-rule.stack.length);
    state.ctxt = new Context(meta_subst);
    return rule.name;
  }

  // Running the dtree using the given arguments (in reverse order)
  exec_dtree(dtree, stack) {
    if (!dtree) { return [null,null]; }
    if (dtree.c === 'Switch') {
      const whnf = this.whnf_state(stack[dtree.index]);
      // whnf should be a fully unfolded (head is not an App) and compressed (not a shift of a shift) state
      switch (whnf.getHeadC()) {
        case 'Lam':
          if (!dtree.Lam) { return this.exec_dtree(dtree.def,stack); }
          stack.push( whnf.getHeadBody() );
          return this.exec_dtree(dtree.Lam,stack);
        case 'Ref':
          if (!dtree.Ref                                   ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Ref[whnf.getHeadName()]               ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Ref[whnf.getHeadName()][whnf.nbArgs()]) { return this.exec_dtree(dtree.def,stack); }
          whnf.forEachArg((e)=>stack.push(e));
          return this.exec_dtree(dtree.Ref[whnf.getHeadName()][whnf.nbArgs()],stack);
        case 'Var':
          if (!dtree.Var                                    ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Var[whnf.getHeadIndex()]               ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Var[whnf.getHeadIndex()][whnf.nbArgs()]) { return this.exec_dtree(dtree.def,stack); }
          whnf.forEachArg((e)=>stack.push(e));
          return this.exec_dtree(dtree.Var[whnf.getHeadIndex()][whnf.nbArgs()], stack);
        case 'MVar':
          return this.exec_dtree(dtree.def,stack);
        default: fail("DTreeExec","Unexpected constructor in switch case: "+whnf.getHeadC());
      }
    } else if (dtree.c === 'Test') {
      const subst = new Map();
      for (let i = 0; i < dtree.match.length; i++) {
        const m = dtree.match[i];
        let matched = stack[m.index];
        if (m.joker_match) {
          // "joker match" : the meta var is applied to all locally bound variables in their DB index order
          // we try to reuse the state if it is applied to the same arguments on the RHS
          matched = new SimpleMatch(matched);
        } else {
          try {
            matched = new ComplexMatch(matched.to_term(), m.subst);
          } catch(e) {
            if (e.title != 'MetaMatchFailed') { throw(e); }
            try {
              //console.log("Computing NF to match", matched.to_term()," with ", m.subst);
              matched = new ComplexMatch( this.nf_state(matched).to_term(), m.subst);
            } catch(e) {
              if (e.title != 'MetaMatchFailed') { throw(e); }
              return this.exec_dtree(dtree.def, stack);
            }
          }
        }
        // Check if the same meta variable was previously matched
        const prev_matched = subst.get(m.name);
        if (prev_matched) {
          // Assuming the matched problem is { t against X[2,1] under 4 lambdas }
          // Then matched.map = [undefined, 1, 0, undefined]  and  matched.term = t
          // Assuming previously matched is { u against X[1,0] under 3 lambdas }
          // Then prev_matched.map = [1, 0, undefined]  and  prev_matched.term = u
          // We need to check that   t <<->> u{ 1 <- 2, 0 <- 1}
          // or, equivalently, that  u <<->> t{ 2 <- 1, 1 <- 0}
          const matched_args = m.args.map( (j) => new State(Var(j)) );
          if (!this.are_convertible(prev_matched.meta_apply(matched_args).to_term(), matched.meta_apply(matched_args).to_term())) {
            return this.exec_dtree(dtree.def,stack);
          }
        } else {
          subst.set(m.name, matched);
        }
      }
      return [dtree.rule, subst];
    } else {
      fail("DTreeExec","Unexpected DTree constructor: "+dtree.c);
    }
  }

  // Checks if two terms are convertible
  are_convertible(u, v) {
    //console.log("Conv:",pp_term(u),"<-?->",pp_term(v));
    const acc = [ [u,v] ];
    while (acc.length > 0) {
      const [a,b] = acc.pop();
      //console.log("Equal:",pp_term(a),"=?=",pp_term(b));
      if (!equals(a,b)) {
        const whnf_a = this.whnf(a);
        const whnf_b = this.whnf(b);
        if (!same_head(whnf_a, whnf_b, acc)) {
          //console.log("Mismatch: ",pp_term(whnf_a)," <-/-> ", pp_term(whnf_b));
          return false;
        }
      }
    }
    return true;
  }
}
