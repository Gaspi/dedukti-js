

// Computes the reduction decision tree for the given rules
// sharing a common head symbol assuming it is meant to be applied
// to an application of this symbol to at least [arity] arguments
function compute_decision_tree(rules, arity) {
  const nb_rules = rules.length;
  if (nb_rules==0) { throw "DTree:\nCannot compute decision tree for an empty set of rules."}
  const smb = rules[0].head;
  const patterns = Array(nb_rules);
  const contexts = Array(nb_rules);
  const lhs      = Array(nb_rules);
  for (let i=0; i<nb_rules; i++) {
    const rule = rules[i];
    if (rule.head != smb) { throw "DTree:\nDifferent head symbols found ["+rule.head+"] and ["+smb+"]."}
    patterns[i] = Array(arity);
    contexts[i] = Array(arity);
    for (let j=0; j<arity; j++) {
      patterns[i][j] = j < rule.stack.length ? rule.stack[j] : Star();
      contexts[i][j] = 0;
    }
    lhs[i] = app(rule)
  }
}

function compute_dtree(patterns, contexts, lhs) {
  
}

// Running
function execute_dtree(dtree,stack) {
}

