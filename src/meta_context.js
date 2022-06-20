
function meta_abstract(ctx, args) {
  // We compute the smallest DB index of the arguments (which are assumed all variables)
  let mini = 0;
  args.forEach(function (a) {
    if (a[c] != 'Var') { fail('MetaAbstract',"Meta-variable's argument should be a locally bounded variable."); }
    mini = Math.min(mini, a.index);
  });
  // Array [mini, mini+1, ..., maxi]
  const nargs = [...Array(ctx_size(ctx)).keys()].slice(mini);
  return nargs;
}


// A context is a list of [name, type] pairs
class MetaContext {
  type = new Map();
  val  = new Map();
  conditions = [];
  
  // Three modes available :
  // - 'def': (default) when checking types in declarations.
  //          metavars are assumed a type when first encountered, no meta_conditions required (?)
  //          metavars are later assigned a value which is checked against the already assumed type
  // - 'lhs': when checking the LHS of a rule :
  //          metavars are assumed types with conditions every time they are encountered
  //          conversion conditions are recorded
  // - 'rhs': when checking the RHS of a rule :
  //          metavars instances are inferred/checked types using already recorded types
  //          conversion conditions are use to check new conditions
  constructor(mode) { this.mode = mode; }
  
  set_type(term, ctx, type) {
    // Compute typing conditions on meta-variables required for the type to be valid
    const meta_conditions = [];
    while (let i = 0; i < ctx.length; i++) {
      // TODO
    }
    const meta_vars = meta_abstract(ctx, term.args);
    const indexes = term.args.map((t)=>t.index);
    // Compute and return the "meta-type" : the meta-term corresponding to [type]
    // where the locally bounded variables arguments are substituted with indexed meta-variables.
    const meta_type = meta_match(type, term.args, 0);
    this.type.set(term.name, {meta_conditions,meta_type});
  }
  
  get_type(mvar) {
    const recorded_type = this.type.get(mvar.name);
    if (!recorded_type) { return null; }
    // TODO
    return recorded_type.meta_type;
  }
  
  set_val(mvar, val) {
    this.val.set(mvar.name, val);
  }
  
  get_val(mvar) {
    const val = this.val.get(mvar.name);
    return meta_subst(val, mvar.args.map((t)=>[t]));
  }
  
}
