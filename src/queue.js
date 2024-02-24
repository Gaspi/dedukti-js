class Queue {
  constructor() {
    this.items = {};
    this.headIndex = 0;
    this.tailIndex = 0;
  }

  enqueue(item) {
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

  peek() {
    this.#validate() // validate if not empty
    return this.items[this.headIndex];
  }

  #validate() { // validation logic
    if (this.headIndex === this.tailIndex) { 
      throw new Error('Cannot perform operation on an empty queue')
    }
  }

  get length() {
    return this.tailIndex - this.headIndex;
  }
}
