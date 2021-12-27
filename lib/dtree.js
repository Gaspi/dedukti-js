// Computes the reduction decision tree for the given rules
// sharing a common head symbol assuming it is meant to be applied
// to an application of this symbol to at least [arity] arguments

function compute_row(rule, arity) {
  return { rule:rule, cols: rule.stack.concat( Array(arity-rule.stack.length).fill(Star()) ) };
}

function compute_decision_tree(rules, arity) {
  if (rules.length==0) { throw "DTree:\nCannot compute decision tree for an empty set of rules." }
  const mismatch = rules.find( (r) => r.head != rules[0].head );
  if (mismatch) { throw "DTree:\nHead symbol mismatch found: ["+mismatch.head+"] != ["+rules[0].head+"]." }
  const patterns = {
    rows   : rules.map( (r) => compute_row(r,arity) ),
    depths : Array(arity).fill(0)
  };
  return compute_dtree(patterns);
}

// Returns a decision tree from the given matrix
function compute_dtree(m) {
  console.log(m);
  if (m.rows.length == 0) { return null; }
  // Find the first column [j] that is not a meta-var in the first row of patterns
  const j = m.rows[0].cols.findIndex((p) => p[c] != "MVar" && p[c] != "Star");
  console.log(j);
  if (j<0) {
    return {[c]:'Test',
        match   : compute_matching_problem(m.rows[0]),
        fallback: compute_dtree({rows:m.rows.slice(1), depth:m.depth})
      }
  } else {
    const res = { [c]:'Switch' };
    for (let i = 0; i < m.rows.length; i++) {
      const row = m.rows[i];
      console.log(row);
      const [pat,stack] = get_head(row.cols[j]);
      switch (pat[c]) {
        case "Lam":
          if (!res.Lam) {
            res.Lam = compute_dtree(specialize_lam(m,j));
          }
          break;
        case "Var":
          if (!res.Var) { res.Var = {}; }
          if (!res.Var[pat.index]) { res.Var[pat.index] = {}; }
          if (!res.Var[pat.index][stack.length]) {
            res.Var[pat.index][stack.length] = compute_dtree(specialize_var(m,j,pat.index,pat.stack.length));
          }
          break;
        case "Ref":
          if (!res.Ref) { res.Ref = {}; }
          if (!res.Ref[pat.name]) { res.Ref[pat.name] = {}; }
          if (!res.Ref[pat.name][stack.length]) {
            res.Ref[pat.name][stack.length] = compute_dtree(specialize_ref(m,j,pat.name,stack.length));
          }
          break;
        default:
          if (!res.def) { res.def = compute_dtree(specialize_def(m,j)); }
      }
    }
    return res;
  }
}



function specialize_lam(m,j) {
  const rows = [];
  for (let i = 0; i < m.rows.length; i++) {
    const row = m.rows[i];
    const ncols = row.cols.slice();
    ncols[j] = Star();
    const [pat,stack] = get_head(row.cols[j]);
    switch (pat[c]) {
      case 'MVar':
      case 'Star':
        rows.push( { cols:ncols.concat([Star()]), rule:row.rule } );
        break;
      case 'Lam':
        rows.push( { cols:ncols.concat([pat.body]), rule:row.rule } );
        break;
    }
  }
  return { rows:rows, depths:m.depths.concat([m.depths[j]+1]) };
}

function specialize_var(m,j,index,nb_args) {
  const rows = [];
  for (let i = 0; i < m.rows.length; i++) {
    const row = m.rows[i];
    const ncols = row.cols.slice();
    ncols[j] = Star();
    const [pat,stack] = get_head(row.cols[j]);
    switch (pat[c]) {
      case 'MVar':
      case 'Star':
        rows.push( { cols:row.cols.concat(Array(nb_args).fill(Star())), rule:row.rule } );
        break;
      case 'Var':
        if (pat.index == index && stack.length == nb_args) {
          rows.push( { cols:row.cols.concat(stack), rule:row.rule } );
        }
        break;
    }
  }
  return { rows:rows, depths:m.depths.concat( Array(nb_args).fill(m.depths[j]) ) };
}

function specialize_ref(m,j,name,nb_args) {
  const rows = [];
  for (let i = 0; i < m.rows.length; i++) {
    const row = m.rows[i];
    const ncols = row.cols.slice();
    ncols[j] = Star();
    const [pat,stack] = get_head(row.cols[j]);
    switch (pat[c]) {
      case 'MVar':
      case 'Star':
        rows.push( { cols:ncols.concat(Array(nb_args).fill(Star())), rule:row.rule } );
        break;
      case 'Ref':
        if (pat.name == name && stack.length == nb_args) {
          rows.push( { cols:ncols.concat(stack), rule:row.rule } );
        }
        break;
    }
  }
  return { rows:rows, depths:m.depths.concat( Array(nb_args).fill(m.depths[j]) ) };
}

function compute_matching_problem(patterns,depths) {
  return null;
}

// Running the dtree using the given arguments in correct order
function execute_dtree(dtree,args) {
  return null;
}

