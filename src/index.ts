
import * as fs from 'node:fs';
import grammar from './grammar'

// Create a Parser object from our grammar.
const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar));
const initial_state = parser.save();

// Convert a string to a series of instructions
function parse(code:string) {
  parser.restore(initial_state);
  parser.feed(code);
  return parser.results[0];
}

function load_module(module_name:string) {
  try {
    return parse( fs.readFileSync(`examples/${module_name}.dk`, 'utf8') );
  } catch (err) {
    console.error(err);
  }
}

function check(txt:string) {
  // Parsing of input text code
  const instructions = parse(txt);
  log({status:'ok',title:"Parsing",msg:"done."});

  // Reseting the signature
  const sig = new Signature();

  // Checking each instructions with the signature
  for (const message of sig.check_instructions(instructions, load_module)) {
    log(message);
  }
  const chrono = (new Date()).getTime() - sig.start_time.getTime();
  log({status:'ok',title:"File Checking",msg:`All done (${chrono}ms) !`});
}


function log(msg:Message):void {
  let ln = "";
  if (msg.ins) {
    while (msg.ins.length > 1) {
      const instruction = msg.ins.pop();
      if (instruction) {
        console.log(`In module [${instruction.module}]`);
      }
    }
    ln = `line:${msg.ins[0].ln}:`;
  }
  console.log(`${ln} [${msg.title}] ${msg.msg}`);
}
