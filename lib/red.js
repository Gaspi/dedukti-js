
function Red() { return new Map(); }

function add_new_rule(red,rule) {
  const [head,stack] = get_head(rule.lhs);
  if (head[c] !== 'Ref') {
    throw 'NewRule:\nUnexpected head symbol in rule left-hand side: '+head[c];
  }
  if (!red[head.name]) { red[head.name] = {rules:[],decision_tree:{},computed:true} ; }
  red[head.name].rules.push(rule);
  red[head.name].computed=false;
}

function compute(rules) {
  // Compute the reduction tree
}

function get_decision_tree(red,name) {
  if (!red[name]) { throw 'Reduction:\nSymbol is unknown to the reduction machine: '+head.name; }
  if (!red[name].computed) {
    red[name].decision_tree = compute(red[name].rules);
    red[name].computed = true;
  }
  return red[name].decision_tree;
}

function reduce(red,[head,stack]) {
  const dtree = get_decision_tree(red,head.name);
  // Perform reduction using the stack
}
