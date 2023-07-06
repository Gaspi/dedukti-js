
function fail(title,msg,ln) { throw {title,msg,ln}; }

// Togglable debug module
const debug = {
  debug_mode: false,
  offset : "",
  enable_log() { this.debug_mode = true; },
  disable_log() { this.debug_mode = false; },
  increment() { this.offset += " "; },
  decrement() { this.offset = this.offset.slice(1); },
  get log() {
    return (this.debug_mode ? console.log : function () {});
  },
  logTxt(txt) {
    if (this.debug_mode) {
      console.log(this.offset+txt);
    }
  }
};
