

const todo = new Queue<[(...args:any[])=>void, any[]]>();

function eval_obj(f : (o:any, ...args:any[])=>void, args=[]) {
  const o:any = {};
  eval_f(f, [o, ...args]);
  return o;
}

function eval_f(f : (...args:any[])=>void, args:any[]=[]) {
  todo.enqueue([f,args]);
}

function eval_all() {
  while (todo.length) {
    const [f,args] = todo.dequeue();
    f(...args);
  }
}
