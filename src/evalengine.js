
const todo = new Queue();

function eval_obj(f, args=[]) {
  const o = {};
  eval_f(f, [o, ...args]);
  return o;
}

function eval_f(f, args=[]) {
  todo.enqueue([f,args]);
}

function eval_all() {
  while (todo.length()) {
    const (f,args) = todo.dequeue();
    f(...args);
  }
}
