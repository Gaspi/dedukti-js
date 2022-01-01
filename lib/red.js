
// Conversion to/from state representation: [head,stack]
function to_state(term) { return get_head(term); }
function from_state([head,stack]) { return stack.reduceRight(App,head); }


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



// Matches all variables to the corresponding meta variable
function meta_match(term, map, depth) {
  function mm(t,d) {
    switch (t[c]) {
      case "Var":
        if (t.index < d || depth == 0) { return t; }
        if (t.index >= d + depth) { return Var(t.index-depth, preferred_name=t.preferred_name); }
        const m = map[t.index -d];
        if (m) { return  m; }
        else { throw {[c]: 'MetaMatchFailed'}; }
      case "All" : return All(t.name, mm(t.dom,d), mm(t.cod,d+1));
      case "Lam" : return Lam(t.name, t.type && mm(t.type,d) , mm(t.body,d+1) );
      case "App" : return App( mm(t.func,d) , mm(t.argm,d) );
      case "MVar": return MVar(t.name, t.args.map( (t)=>mm(t,d) ));
      default: return t;
    }
  }
  return mm(term,0);
}

class ReductionEngine {
  red = new Map();
  
  constructor() {}
  
  add_new_rule(rule) {
    // Find the head symbol and the stack of the rule
    const [head,stack] = get_head(rule.lhs);
    if (head[c] !== 'Ref') {
      throw 'Scope:\nUnexpected head symbol in rule left-hand side: '+head[c];
    }
    rule.head = head.name;
    rule.stack = stack;
    // Add a new entry for a newly rewritten symbol
    if (!this.red.get(rule.head)) {
      this.red.set(rule.head, { rules:[], decision_trees:[] });
    }
    // The new rule is added to the global set of rules for that symbol
    this.red.get(rule.head).rules.push(rule);
    const dts = this.red.get(rule.head).decision_trees;
    const arity = stack.length;
    // All DTs of arity greater than that of the new rule are erased
    // (to be recomputed taking into account the new rule)
    for (let i = arity; i < dts.length; i++) { dts[i] = null; }
    // Empty DTs are generated for arities up to that of the new rule
    for (let i = dts.length; i <= arity; i++) { dts.push(null); }
  }
  
  
  // throw 'Reduction:\nSymbol is unknown to the reduction machine: '+name;
  get_decision_tree(name,arity) {
    const r = this.red.get(name);
    if (!r) { return null; }
    const dts = r.decision_trees;
    if (arity >= dts.length) { arity = dts.length-1; }
    if (!dts[arity]) {
      const [rules, max_arity] = filter_rules(r.rules, arity);
      if (!dts[max_arity]) {
        dts[max_arity] = compute_decision_tree(rules, max_arity);
      }
      if (max_arity < arity) {
        dts[arity] = dts[max_arity];
      }
    }
    return dts[arity];
  }
  
  // Reduces a term until a normal form is found
  whnf(term) { return from_state( this.whnf_state( to_state(term) ) ); }
    nf(term) { return from_state( this.nf_state(   to_state(term) ) ); }
  
  // Computes the strong normal form of term given in state representation: [head,stack]
  // Updates the [state] Array in place
  nf_state(state) {
    const [head,stack] = this.whnf_state(state);
    for (let i=0; i<stack.length;i++) { stack[i] = this.nf(stack[i]); };
    switch (head[c]) {
      case "All":
        head.dom = this.nf(head.dom);
        head.cod = this.nf(head.cod);
        break;
      case "Lam":
        head.type = this.nf(head.type);
        head.body = this.nf(head.body);
        break;
      case "MVar":
        for (let i = 0; i < head.args.length; i++) {
          head.args[i] = this.nf(head.args[i]);
        }
        break;
    }
    return [head,stack];
  }
  
  // Computes the weak head normal form of term given in state representation: [head,stack]
  // Updates the [state] Array in place
  whnf_state(state) {
    while (true) {
      const [head,stack] = state;
      switch (head[c]) {
        case "Lam":
          if (stack.length == 0) { return state; } // Unapplied lambda
          state[0] = subst(head.body, stack.pop()); // Beta reduction
          //console.log("WHNF: Beta");
          break;
        case "Ref": // Rewriting
          const rule_name = this.head_rewrite(state);
          if (!rule_name) { return state; }
          //console.log("WHNF: ",rule_name);
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
    let [rule, subst] = this.exec_dtree(dtree.tree,truncated_stack);
    if (!rule) { return null; }
    const [rhead, rstack] = to_state( meta_subst(rule.rhs, subst) );
    state[0] = rhead;
    state[1] = stack.slice(0,stack.length-rule.stack.length).concat(rstack);
    return rule.name;
  }
  
  // Running the dtree using the given arguments (in reverse order)
  exec_dtree(dtree, stack) {
    if (!dtree) { return [null,null]; }
    if (dtree[c] == 'Switch') {
      const hstate = to_state(stack[dtree.index])
      const [head,hstack] = this.whnf_state(hstate);
      switch (head[c]) {
        case 'Lam':
          if (!dtree.Lam) { return this.exec_dtree(dtree.def,stack); }
          stack.push(head.body);
          return this.exec_dtree(dtree.Lam,stack);
        case 'Ref':
          if (!dtree.Ref                          ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Ref[head.name]               ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Ref[head.name][hstack.length]) { return this.exec_dtree(dtree.def,stack); }
          hstack.forEach((e)=>stack.push(e));
          return this.exec_dtree(dtree.Ref[head.name][hstack.length],stack);
        case 'Var':
          if (!dtree.Var                           ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Var[head.index]               ) { return this.exec_dtree(dtree.def,stack); }
          if (!dtree.Var[head.index][hstack.length]) { return this.exec_dtree(dtree.def,stack); }
          hstack.forEach((e)=>stack.push(e));
          return this.exec_dtree(dtree.Var[head.index][hstack.length], stack);
      }
    } else if (dtree[c] == 'Test') {
      const subst = {};
      for (let i = 0; i < dtree.match.length; i++) {
        const m = dtree.match[i];
        const matched = meta_match( stack[m.index], m.args, m.depth);
        if (subst[m.name]) {
          if (!are_convertible(subst[m.name][0], matched)) {
            return this.exec_dtree(dtree.def,stack);
          }
        } else {
          subst[m.name] = [matched];
        }
      }
      return [dtree.rule, subst];
    } else {
      throw "DTreeExec:\nUnexpected DTree constructor: "+dtree[c];
    }
  }
  
  // Checks if two terms are equal
  are_convertible(u, v) {
    const acc = [ {a:u,b:v} ];
    while (acc.length > 0) {
      const {a,b} = acc.pop();
      if (equals(a,b)) { continue; }
      if (!same_head( this.whnf(a) , this.whnf(b) ,acc)) { return false; }
    }
    return true;
  }
}
