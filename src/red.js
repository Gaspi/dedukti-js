
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

/** A term representation with:
    - with easy access to its head
    - reducable in place
    - includes a meta-substition and a variable substitution
 */
class State {
  constructor(term, ctxt = new Context()) {
    this.head = term;
    // The stack may be modified in place
    this.stack = [];
    // The context may be shared among states and should not be modified in place
    this.ctxt = ctxt;
    // Array of shifted term representations of the state. Should be reset every time the state is updated
    this.terms = [];
    this.heads = [];
  }
  
  // Term conversion with memoisation of shifted versions of head and global terms to avoid recomputing and have maximum sharing
  _to_term(s=0) {
    if (!this.heads[s]) {
      if (!this.heads[0]) {
        this.heads[0] = this.context.apply(this.head);
      }
      this.heads[s] = shift(this.heads[0], s);
    }
    return this.stack.map( (e)=>e.to_term(s) ).reduceRight(App, this.heads[s] );
  }
  
  // Memoised version
  to_term(s=0) {
    if (!this.terms[s]) {
      this.terms[s] = this._to_term(s);
    }
    return this.terms[s];
  }
  
  link_to(state) {
    ...
  }
}

class ShiftedState {
  constructor(state, shift=1) {
    this.state = state;
    this.shift = shift;
    this.compress();
  }
  
  // Graph compression
  compress() {
    if (this.state instanceof ShiftedState) {
      this.state = state.state;
      this.shift = state.shift+shift;
    }
  }
  
  // Overriding term conversion
  to_term(s=0) {
    this.compress();
    return (this.state == null) ? null: this.state.to_term(s+this.shift);
  }
}


// A context is a mapping both of meta-variables and variables of a term
// to states (which can be computed to term if needed)
// It can be applied to terms.
class Context {
  constructor(meta=new Map(), depth=0, subst=[]) {
    this.meta = meta;
    this.depth = depth;
    // Depth of the meta substitution
    // Should be equal to the number of null in subst
    this.subst = subst;
  }
  
  function extend(s) {
    return new Context( this.meta, this.depth  , this.subst.concat(s) );
  }
  
  function shift_extend() {
    return new Context( this.meta, this.depth+1, this.subst.map((s) => new ShiftedState(s,1)).concat( new ShiftedState(null,0) ), );
  }
  
  apply(term, depth=0) {
    const varshift = this.subst.length - this.depth;
    // Compteur de substitutions
    let ct = 0;
    function e(t,d) {
      const cta = ct;
      if (t.c === "MVar") {
        const args = t.args.map( (t)=>e(t,d) );
        const msubst_t = this.meta.get(t.name);
        if (!msubst_t) {
          return (ct === cta ? t : MVar(t.name, args));
        } else {
          ct += 1; // Meta-substitution effectuée
          const subst_ctxt = new Context(new Map(), 0, args);
          const subst_mt = subst_ctxt.apply(msubst_t)
          return shift(subst_mt, d+this.depth);
        }
      } else if (t.c === "Var") {
        const db = t.index - d;
        if (db < 0) { // Locally bounded variable
          return t;
        } else if (db >= this.subst.length) { // Free variable
          if (varshift == 0) {
            return t;
          } else {
            ct += 1; // Shifting effectué
            return Var(t.index - varshift);
          }
        } else {
          const st = this.subst[db];
          const te = st.to_term(d);
          if (te == null) {
            if (db == st.shift) {
              return t; //
            } else {
              ct += 1; // Shifting effectué sur une variable localement liées mais sous un lambda substitué
              return Var(t.index - db + st.shift);
            }
          } else {
            ct += 1; // Substitution effectuée
            return te;
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
  red = new Map();
  constructor() {}
  
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
      fail("ConstantDecl","The symbol `"+name+"` is not constant.");
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
    nf(term) { return this.nf_state(   new State(term) ).to_term(); }
  
  // Computes the strong normal form of term given in state representation: [head,stack]
  // Updates the [state] Array in place
  nf_state(state) {
    this.whnf_state(state);
    for (let i=0; i < state.stack.length; i++) { state.stack[i] = this.nf(state.stack[i]); };
    switch (state.head.c) {
      case "All":
        state.head = All(state.head.name, this.nf(state.head.dom), this.nf(state.head.cod));
        break;
      case "Lam":
        state.head = Lam(state.head.name, this.nf(state.head.type), this.nf(state.head.body));
        break;
      case "MVar":
        state.head = MVar(state.head.name, state.args.map(this.nf));
        break;
    }
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
      if (state instanceof ShiftedState) {
        whnf_state(state.state);
        return state;
      }
      switch (state.head.c) {
        case "App":
          // Push the state version of the argument on the stack
          state.stack.push( new State(state.head.argm, state.ctxt) );
          state.head = state.head.func;
          break;
        case "Lam":
          // Unapplied lambda is a WHNF
          if (state.stack.length === 0) { return state; }
          // Otherwise add the top stack argument to the substitution
          // and compute the WHNF of the body (\x.t) u1 u2 ... --> t[x\u1] u2 ...
          state.head = state.head.body;
          state.ctxt = state.ctxt.extend( state.stack.pop()];
          break;
        case "Ref": // Potential redex
          const rule_name = this.head_rewrite(state);
          // If rewriting occured, proceed with current state, otherwise return
          if (!rule_name) { return state; }
          break;
        case "MVar":
          const msubst_t = state.ctxt.meta.get( state.head.name );
          if ( msubst_t ) {
            const args = state.args.map( (t)=>new State(t,state.ctxt) );
            const ctxt = new Context(new Map(), 0, args);
            let nstate = new State(msubst_t, ctxt);
            if (state.ctxt.depth > 0) {
              nstate = new ShiftedState(nstate, state.ctxt.depth);
            }
            return whnf_state( nstate );
          } else {
            return state;
          }
          break;
        case "Var":
          if (state.ctxt.subst[state.head.index]) {
            return whnf_state( state.ctxt.subst[state.head.index] );
          }
          break;
        default: return state; // Any other construction
      }
    }
  }

  // Applies a (single) rewrite step at the head if any rule matches at the head
  // Updates [state] in place and returns the name of the rule used or null if no step was performed
  head_rewrite(state) {
    // Getting the head symbol's decision tree
    let [head,stack] = state;
    const dtree = this.get_decision_tree(head.name, stack.length);
    if (!dtree) { return null; }
    // Truncate to keep only the first [arity] arguments from the top of the stack
    const truncated_stack = stack.slice(stack.length-dtree.arity);
    // Running the decision tree with the given args (in order)
    let [rule, meta_subst] = this.exec_dtree(dtree.tree,truncated_stack);
    if (!rule) { return null; }
    state.head = rule.rhs;
    state.stack = stack.slice(0,stack.length-rule.stack.length);
    state.ctxt = new Context([], meta_subst);
    return rule.name;
  }
  
  // Running the dtree using the given arguments (in reverse order)
  exec_dtree(dtree, stack) {
    if (!dtree) { return [null,null]; }
    if (dtree.c === 'Switch') {
      const [head,hstack,subst,msubst] = this.whnf_state(stack[dtree.index]);
      switch (head.c) {
        case 'Lam':
          if (!dtree.Lam) { return this.exec_dtree(dtree.def,stack); }
          stack.push( [head.body,[],subst,msubst] );
          return this.exec_dtree(dtree.Lam,stack);
        case 'Ref':
          if (!dtree.Ref                          ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Ref[head.name]               ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Ref[head.name][hstack.length]) { return this.exec_dtree(dtree.def,stack); }
          hstack.forEach((e)=>stack.push(e));
          
          // TODO: 
          return this.exec_dtree(dtree.Ref[head.name][hstack.length],stack);
        case 'Var':
          if (!dtree.Var                           ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Var[head.index]               ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Var[head.index][hstack.length]) { return this.exec_dtree(dtree.def,stack); }
          hstack.forEach((e)=>stack.push(e));
          return this.exec_dtree(dtree.Var[head.index][hstack.length], stack);
        case 'MVar':
          return this.exec_dtree(dtree.def,stack);
        default: fail("DTreeExec","Unexpected constructor in switch case: "+head.c);
      }
    } else if (dtree.c === 'Test') {
      const subst = new Map();
      for (let i = 0; i < dtree.match.length; i++) {
        let m = dtree.match[i];
        let matched = stack[m.index];
        if (!m.joker_match) { // TODO : implement joker match
          // In case of "joker match" (meta var fully applied to locally bounded *in the DB index order*) :
          // the state is already the matched version
          try {
            matched = meta_match(matched.to_term(), m.args);
          } catch(e) {
            if (e.title == 'MetaMatchFailed') {
              try {
                matched = meta_match( this.nf_state(matched).to_term(), m.args);
              } catch(e) {
                if (e.title == 'MetaMatchFailed') {
                  return this.exec_dtree(dtree.def, stack);
                } else { throw e; }
              }
            }
          }
        }
        if (subst.get(m.name)) {
          if (!this.are_convertible(subst.get(m.name), matched)) {
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
  
  // Checks if two terms are equal
  are_convertible(u, v) {
    const acc = [ [u,v] ];
    while (acc.length > 0) {
      const [a,b] = acc.pop();
      if (!equals(a,b) && !same_head( this.whnf(a) , this.whnf(b) , acc )) { return false; }
    }
    return true;
  }
}
