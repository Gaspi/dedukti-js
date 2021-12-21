
function Env() { return new Map(); }

function get(env, fullname, create=false) {
  let venv = env;
  const quals = fullname.split('.');
  const name = quals.pop();
  for (let i = 0; i < quals.length; i++) {
    if (!venv[quals[i]]) {
      if (create) {
        venv[quals[i]] = new Env();
      } else {
        return undefined;
      }
    }
    venv = venv[quals[i]];
  }
  if (!venv[name] && create) {
    venv[name] = {fullname:fullname, rules:[]};
  } else if (create) {
    throw "Env:\nAlready defined reference: `" + fullname + "`.";
  }
  return venv[name];
}

function do_get(env, fullname) {
  const res = get(env, fullname);
  if (res) { return res; }
  else { throw "Env:\nUndefined reference: `" + fullname + "`."; };
}


function add_new_symbol(env, fullname, type) {
  get(env, fullname, create=true).type = type;
}
