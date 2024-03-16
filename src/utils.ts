
function fail(title:string, msg:string, ln?:number): never { throw {title,msg,ln}; }

// Togglable debug module
const debug = {
  debug_mode: false,
  offset : "",
  enable_log() { this.debug_mode = true; },
  disable_log() { this.debug_mode = false; },
  increment() { this.offset += " "; },
  decrement() { this.offset = this.offset.slice(1); },
  get log() : (x:string) => void {
    return (this.debug_mode ? console.log : function () {});
  },
  logTxt(txt : string) {
    if (this.debug_mode) {
      console.log(this.offset+txt);
    }
  }
};
