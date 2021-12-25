
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
  if (!red.get(head)) {
    red.set(head, { rules:[], decision_trees:[] });
  }
  // The new rule is added to the global set of rules for that symbol
  red.get(head).rules.push(rule);
  const dts = red.get(head).decision_trees;
  const arity = stack.length;
  // All DTs of arity greater than that of the new rule are erased
  // (to be recomputed taking into account the new rule)
  for (let i = arity; i < dts.length; i++) { dts[i] = null; }
  // Empty DTs are generated for arities up to that of the new rule
  for (let i = dts.length; i <= arity; i++) { dts.push(null); }
}

function filter_rules(rules,arity) {
  const res = [];
  let max = null;
  for (let i = 0; i < rules.length; i++) {
    const ar = rules[i].stack.length;
    if (ar > max) { max = ar; }
    if (ar <= arity) { res.push(rules[i]); }
  }
  return [ res , max ];
}

// throw 'Reduction:\nSymbol is unknown to the reduction machine: '+name;
function get_decision_tree(red,name,arity) {
  const dt = red.get(name);
  if (!dt) { return null; }
  if (arity >= dt.length) { arity = length-1; }
  if (!dt[arity]) {
    const [rules, max_arity] = filter_rules(dt.rules, arity);
    if (!dt[max_arity]) {
      dt[max_arity] = compute_decision_tree(dt.rules, max_arity);
    }
    if (max_arity < arity) {
      dt[arity] = dt[max_arity];
    }
  }
  return dt[arity];
}



// Reduces a term until a normal form is found
function whnf(term, red) {
  const [ head,  stack] = get_head(term);
  const [nhead, nstack] = whnf_state([head,stack], red);
  return app(head,stack);
}

function whnf_state(state, red) {
  const [head,stack] = state;
  switch (head[c]) {
    case "Var":
    case "Typ":
    case "Knd":
    case "Star":
    case "All":
    case "MVar": return state;
    case "Lam":
      if (stack.length == 0) { return state; }
      const arg = stack.pop()
      return [ subst(head.body, arg), arg ]
    case "Ref":
      return head_rewrite(state,red)
    default: throw "Norm:\nUnexpected constructor to normalize:"+term[c];
  }
}

function nf(term, red) {
  // TODO
  return term;
}

function head_rewrite(state,red) {
  // Getting the head symbol's decision tree
  let [head,stack] = state;
  const dtree = get_decision_tree(red, head.name, stack.length);
  if (!dtree) { return state; }
  // Retrieving the first [arity] arguments from the top of the stack
  const rw_stack = [];
  for(let i=0; i<dtree.arity; i++) { rw_stack.push(stack.pop()); }
  // Running the decision tree with the stack
  let reduct = execute_dtree(dtree,rw_stack);
  // Returning the reduct together with the remaining stack
  return [reduct,stack];
}
