class Queue<T> {
  items : { [key:number]: T } = {};
  headIndex = 0;
  tailIndex = 0;
  constructor() {}

  enqueue(item:T) {
    this.items[this.tailIndex] = item;
    this.tailIndex++;
  }

  dequeue() {
    this.#validate() // validate if not empty
    const item = this.items[this.headIndex];
    delete this.items[this.headIndex];
    this.headIndex++;
    return item;
  }

  peek() : T {
    this.#validate() // validate if not empty
    return this.items[this.headIndex];
  }

  #validate() : void { // validation logic
    if (this.headIndex === this.tailIndex) { 
      throw new Error('Cannot perform operation on an empty queue')
    }
  }

  get length() : number {
    return this.tailIndex - this.headIndex;
  }
}
