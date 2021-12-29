
function Red() { return new Map(); }

function add_new_rule(red,rule) {
  // Find the head symbol and the stack of the rule
  const [head,stack] = get_head(rule.lhs);
  if (head[c] !== 'Ref') {
    throw 'Scope:\nUnexpected head symbol in rule left-hand side: '+head[c];
  }
  rule.head = head.name;
  rule.stack = stack;
  // Add a new entry for a newly rewritten symbol
  if (!red.get(rule.head)) {
    red.set(rule.head, { rules:[], decision_trees:[] });
  }
  // The new rule is added to the global set of rules for that symbol
  red.get(rule.head).rules.push(rule);
  const dts = red.get(rule.head).decision_trees;
  const arity = stack.length;
  // All DTs of arity greater than that of the new rule are erased
  // (to be recomputed taking into account the new rule)
  for (let i = arity; i < dts.length; i++) { dts[i] = null; }
  // Empty DTs are generated for arities up to that of the new rule
  for (let i = dts.length; i <= arity; i++) { dts.push(null); }
}

function filter_rules(rules,arity) {
  const res = [];
  let max = -1;
  for (let i = 0; i < rules.length; i++) {
    const ar = rules[i].stack.length;
    if (ar > max) { max = ar; }
    if (ar <= arity) { res.push(rules[i]); }
  }
  return [ res , max ];
}

// throw 'Reduction:\nSymbol is unknown to the reduction machine: '+name;
function get_decision_tree(red,name,arity) {
  const r = red.get(name);
  if (!r) { return null; }
  const dts = r.decision_trees;
  if (arity >= dts.length) { arity = dts.length-1; }
  if (!dts[arity]) {
    const [rules, max_arity] = filter_rules(r.rules, arity);
    if (!dts[max_arity]) {
      dts[max_arity] = compute_decision_tree(r.rules, max_arity);
    }
    if (max_arity < arity) {
      dts[arity] = dts[max_arity];
    }
  }
  return dts[arity];
}


// Conversion to/from state representation: [head,stack]
function to_state(term) { return get_head(term); }
function from_state([head,stack]) { return stack.reduceRight(App,head); }

// Reduces a term until a normal form is found
function whnf(term, red) {
  const state = to_state(term);
  whnf_state(state, red);
  return from_state(state);
}

function nf(term, red) {
  const [head, stack] = nf_state(to_state(term), red);
  return app(head, stack);
}

// Computes the strong normal form of term given in state representation: [head,stack]
// Updates the [state] Array in place
function nf_state(state, red) {
  whnf_state(state, red);
  const [head,stack] = state;
  for (let i=0; i<stack.length;i++) { stack[i] = nf(stack[i],red); };
  switch (head[c]) {
    case "All":
      head.dom = nf(head.dom, red);
      head.cod = nf(head.cod, red);
      break;
    case "Lam":
      head.type = nf(head.type, red);
      head.body = nf(head.body, red);
      break;
    case "MVar":
      for (let i = 0; i < head.args.length; i++) {
        head.args[i] = nf(head.args[i], red);
      }
      break;
  }
  return [head,stack];
}

// Computes the weak head normal form of term given in state representation: [head,stack]
// Updates the [state] Array in place
function whnf_state(state, red) {
  while (true) {
    const [head,stack] = state;
    switch (head[c]) {
      case "Lam":
        if (stack.length == 0) { return state; } // Unapplied lambda
        state[0] = subst(head.body, stack.pop()); // Beta reduction
        console.log("Beta");
        break;
      case "Ref": // Rewriting
        const rule_name = head_rewrite(state, red);
        if (!rule_name) { return state; }
        console.log(rule_name);
        break;
      default: return state; // Any other construction
    }
  }
}

// Applies a (single) rewrite step at the head if any rule matches at the head
// Updates [state] in place and returns the name of the rule used or null if no step was performed
function head_rewrite(state, red) {
  // Getting the head symbol's decision tree
  let [head,stack] = state;
  const dtree = get_decision_tree(red, head.name, stack.length);
  if (!dtree) { return false; }
  // Truncate to keep only the first [arity] arguments from the top of the stack
  const truncated_stack = stack.slice(-dtree.arity);
  // Running the decision tree with the given args (in order)
  let [reduct,rule_name] = execute_dtree(dtree.tree,truncated_stack, red);
  if (rule_name) {
    const [rhead, rstack] = to_state(reduct)
    state[0] = rhead;
    state[1] = stack.slice(0,-dtree.arity).concat(rstack);
  }
  return rule_name;
}


// Running the dtree using the given arguments (in reverse order)
function execute_dtree(dtree, stack, red) {
  if (!dtree) { return [null,null]; }
  if (dtree[c] == 'Switch') {
    const hstate = to_state(stack[dtree.index])
    const [head,hstack] = whnf_state(hstate, red);
    switch (head[c]) {
      case 'Lam':
        if (!dtree.Lam) { return execute_dtree(dtree.def,stack,red); }
        stack.push(head.body);
        return execute_dtree(dtree.Lam,stack,red);
      case 'Ref':
        if (!dtree.Ref                          ) { return execute_dtree(dtree.def,stack,red); }
        if (!dtree.Ref[head.name]               ) { return execute_dtree(dtree.def,stack,red); }
        if (!dtree.Ref[head.name][hstack.length]) { return execute_dtree(dtree.def,stack,red); }
        hstack.forEach((e)=>stack.push(e));
        return execute_dtree(dtree.Ref[head.name][hstack.length],stack,red);
      case 'Var':
        if (!dtree.Var                           ) { return execute_dtree(dtree.def,stack,red); }
        if (!dtree.Var[head.index]               ) { return execute_dtree(dtree.def,stack,red); }
        if (!dtree.Var[head.index][hstack.length]) { return execute_dtree(dtree.def,stack,red); }
        hstack.forEach((e)=>stack.push(e));
        return execute_dtree(dtree.Var[head.index][hstack.length], stack, red);
    }
  } else if (dtree[c] == 'Test') {
    const subst = {};
    for (let i = 0; i < dtree.match.length; i++) {
      console.log(subst);
      const m = dtree.match[i];
      const matched = meta_match( stack[m.index], m.depth); // TODO perform HO matching
      if (subst[m.name]) {
        if (!are_convertible(subst[m.name][0], matched)) {
          return execute_dtree(dtree.def,stack,red);
        }
      } else {
        subst[m.name] = [matched];
      }
    }
    console.log(dtree);
    console.log(subst);
    return [meta_subst(dtree.rhs, subst), dtree.rule_name]
  } else {
    throw "DTreeExec:\nUnexpected DTree constructor: "+dtree[c];
  }
}
