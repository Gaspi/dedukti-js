/**
 * @file 
 *   Decision-tree based rewrite engine.
 * 
 */


/** Builds the row of the matching matrix corresponding to the given rule
 * 
 * @param {object} rule
 *   The rule used to build the row. If its stack is too short it is completed
 * @param {int} arity
 *   Number of columns: should be higher than the rule's stack length
 * 
 */
function compute_row(rule, arity) {
  return { rule:rule, cols: Array(arity-rule.stack.length).fill(Joker()).concat(rule.stack) };
}

/** Computes the reduction decision tree for the given set of rules
 * sharing a common head symbol assuming it is meant to be applied
 * to an application of this symbol to at least [arity] arguments.
 * 
 * @param {Array} rules
 *   Array of the rules to compute with a decision tree.
 * @param {int} arity
 *   Minimum number of arguments the DTree will be expecting.
 * @return
 *   A reduction decision tree ready to be used.
 */
function compute_decision_tree(rules, arity) {
  if (rules.length==0) { fail("DTree","Cannot compute decision tree for an empty set of rules."); }
  const mismatch = rules.find( (r) => r.head != rules[0].head );
  if (mismatch) { fail("DTree","Head symbol mismatch found: ["+mismatch.head+"] != ["+rules[0].head+"]."); }
  const matrix = {
    rows   : rules.map( (r) => compute_row(r,arity) ),
    depths : Array(arity).fill(0)
  };
  return {c:'DTree',arity:arity,tree:compute_dtree(matrix)};
}

/** Computes a decision tree from the given matrix.
 * 
 * @param {Array} m
 *   Array of matrix rows.
 * @return
 *   A reduction decision tree ready to be used.
 */
function compute_dtree(m) {
  if (m.rows.length == 0) { return null; }
  // Find the first column [j] that is not a meta-var in the first row of patterns
  const j = m.rows[0].cols.findIndex((p) => p.c != "MVar");
  if (j<0) {
    return compute_matching_problem(m.rows[0], m.depths,
      def=compute_dtree({rows:m.rows.slice(1), depths:m.depths.slice(1)}));
  } else {
    const res = { c:'Switch', index:j };
    for (let i = 0; i < m.rows.length; i++) {
      const row = m.rows[i];
      const [pat,stack] = get_head(row.cols[j]);
      switch (pat.c) {
        case "Lam":
          if (!res.Lam) {
            res.Lam = specialize(m,j,'Lam',null,1);
          }
          break;
        case "Var":
          if (!res.Var) { res.Var = {}; }
          if (!res.Var[pat.index]) { res.Var[pat.index] = {}; }
          if (!res.Var[pat.index][stack.length]) {
            res.Var[pat.index][stack.length] = specialize(m,j,'Var',pat.index,pat.stack.length);
          }
          break;
        case "Ref":
          if (!res.Ref) { res.Ref = {}; }
          if (!res.Ref[pat.name]) { res.Ref[pat.name] = {}; }
          if (!res.Ref[pat.name][stack.length]) {
            res.Ref[pat.name][stack.length] = specialize(m,j,'Ref',pat.name,stack.length);
          }
          break;
        default:
          if (!res.def) { res.def = specialize(m,j,null,null,0); }
      }
    }
    return res;
  }
}

function specialize_row(cols,j,cons,name,extra_cols) {
  const [pat,stack] = get_head(cols[j]);
  if (pat.c == 'MVar') {
    return cols.concat(Array(extra_cols).fill(Joker()));
  }
  if (pat.c != cons) { return null; }
  if (cons!='Lam' && ( (pat.name || pat.index) != name || stack.length != extra_cols)) { return null; }
  const ncols = cols.concat( cons == 'Lam' ? [pat.body] : stack );
  ncols[j] = Joker();
  return ncols;
}

function specialize(m,j,cons,index,extra_cols) {
  const rows = [];
  for (let i = 0; i < m.rows.length; i++) {
    const cols = specialize_row(m.rows[i].cols,j,cons,index,extra_cols);
    if (cols) { rows.push( { cols:cols, rule:m.rows[i].rule } ); }
  }
  return compute_dtree({
    rows:rows,
    depths:m.depths.concat( Array(extra_cols).fill(m.depths[j]+(cons=='Lam'?1:0)))
    });
}

function compute_matching_problem(row,depths,def=null) {
  const mvars = [];
  for (let i = 0; i < row.cols.length; i++) {
    const p = row.cols[i];
    if (p.c == 'MVar' && !p.joker) {
      mvars.push({
        index:i,
        name:p.name,
        subst:get_meta_match(p.args, depths[i]),
        depth:depths[i],
        args: p.args
        });
    }
  }
  return { c:'Test', match:mvars, rule:row.rule, def:def };
}


function pp_dtrees(dtrees) {
  let res = "Count arguments:\n";
  function pp(t,s) { res+='  '.repeat(t)+s+"\n"; }
  function pp_dtree(dtree,t) {
    if (!dtree) { pp(t,"Fail"); return; }
    if (dtree.c === 'Switch') {
      pp(t,"Look stack["+dtree.index+"]:");
      if (dtree.Lam) {
        pp(t,"Case Lam:");
        pp_dtree(dtree.Lam,t+1);
      }
      if (dtree.Ref) {
        Object.entries(dtree.Ref).forEach(([ref,dts])=>
          Object.entries(dts).forEach(function([ar,dt]) {
            pp(t,"Case `"+ref+"`("+ar+" args):");
            pp_dtree(dt,t+1);
          })
        );
      }
      if (dtree.Var) {
        Object.entries(dtree.Ref).forEach(([ind,dts])=>
          Object.entries(dts).forEach(function([ar,dt]) {
            pp(t,"Case #"+ind+"("+ar+" args):");
            pp_dtree(dt,t+1);
          })
        );
      }
    } else if (dtree.c === 'Test') {
      pp(t,"Match:");
      dtree.match.forEach((m)=>
        pp(t,""+m.name+"["+Object.keys(m.args).map(pp_term).join(', ')+"] = stack["+m.index+"]")
      );
      pp(t,"> Fire rule `"+dtree.rule.name+"`: "+pp_term(dtree.rule.rhs));
    } else {
      fail("PPDTree","Unexpected constructor in dtree: "+dtree.c);
    }
    pp(t,"Default:");
    pp_dtree(dtree.def, t+1);
  }
  
  for (let i = 0; i < dtrees.length; i++) {
    res+="Case "+i+":\n";
    if (dtrees[i]) { pp_dtree(dtrees[i].tree,1); }
    else { res += "  not computed yet...\n"; }
  }
  return res;
}
