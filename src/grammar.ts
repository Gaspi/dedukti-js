// Generated automatically by nearley, version 2.20.1
// http://github.com/Hardmath123/nearley
// Bypasses TS6133. Allow declared but unused functions.
// @ts-ignore
function id(d: any[]): any { return d[0]; }
declare var COLON: any;
declare var CMD_CONST: any;
declare var CMD_THM: any;
declare var DEF: any;
declare var CMD_INJ: any;
declare var LONGARROW: any;
declare var LONGFATARROW: any;
declare var CMD_REQ: any;
declare var CMD_EVAL: any;
declare var CMD_INFER: any;
declare var CMD_CHECK: any;
declare var CONV: any;
declare var NCONV: any;
declare var CMD_PRINT: any;
declare var CMD_DTREE: any;
declare var CMD_TIME: any;
declare var CMD_DEBUGON: any;
declare var CMD_DEBUGOFF: any;
declare var ID: any;
declare var MID: any;
declare var END: any;
declare var LEFTSQU: any;
declare var RIGHTSQU: any;
declare var ENT: any;
declare var COMMA: any;
declare var LEFTPAR: any;
declare var RIGHTPAR: any;
declare var JOKER: any;
declare var TYPE: any;
declare var KIND: any;
declare var QID: any;
declare var DB_INDEX: any;
declare var ARROW: any;
declare var FATARROW: any;


type Lexer = moo.Lexer & {ignoreSet : Set<string|undefined>}

function makeLexer(tokens: moo.Rules, ignoreTokens: string[]) {
  let lexer : Lexer = moo.compile(tokens) as Lexer;
  lexer.ignoreSet = new Set(ignoreTokens);
  let oldnext = lexer.next;
  lexer.next = function () {
    while (true) {
      let token = oldnext.call(this);
      // moo oldnext iterator returns undefined when finished
      if (token == undefined || !this.ignoreSet.has(token.type)) {
        return token;
      } 
      //console.error("ignoring token "+token.type);
    }
  };
  return lexer;
}

const lexer = makeLexer({
    _:{match: /\s+/, lineBreaks: true},
    COMMENT: /\/\/.*?$/,
    DOT     :'.',
    COMMA   :',',
    ARROW   :'->',
    FATARROW:'=>',
    LONGARROW:'-->',
    LONGFATARROW:'==>',
    DEF     :':=',
    ENT :'|-',
    CONV    :'==',
    NCONV   :'!=',
    COLON   :':',
    LEFTSQU :'[',
    RIGHTSQU:']',
    LEFTBRA :'{',
    RIGHTBRA:'}',
    LEFTPAR :'(',
    RIGHTPAR:')',
    JOKER   :'*',
    END     :';',
    TYPE:"Type",
    KIND:"Kind",
    CMD_REQ  :"#REQUIRE",
    CMD_EVAL :"#EVAL",
    CMD_INFER:"#INFER",
    CMD_CHECK:"#CHECK",
    CMD_CONST:"#CONST",
    CMD_THM  :"#THM",
    CMD_INJ  :"#INJECTIVE",
    CMD_PRINT:"#PRINT",
    CMD_DTREE:"#DTREE",
    CMD_TIME :"#TIME",
    CMD_DEBUGON :"#DEBUGON",
    CMD_DEBUGOFF:"#DEBUGOFF",
    DB_INDEX:/\#[0-9]+/,
    MID: /"[^"]*"/,
    QID: /(?:[a-zA-Z0-9_!?'/@]+\.)+[a-zA-Z0-9_!?'/@]+/,
    ID: /[a-zA-Z0-9_!?'/@]+/,
  }, ['_','COMMENT']);


interface NearleyToken {
  value: any;
  [key: string]: any;
};

interface NearleyLexer {
  reset: (chunk: string, info: any) => void;
  next: () => NearleyToken | undefined;
  save: () => any;
  formatError: (token: never) => string;
  has: (tokenType: string) => boolean;
};

interface NearleyRule {
  name: string;
  symbols: NearleySymbol[];
  postprocess?: (d: any[], loc?: number, reject?: {}) => any;
};

type NearleySymbol = string | { literal: any } | { test: (token: any) => boolean };

interface Grammar {
  Lexer: NearleyLexer | undefined;
  ParserRules: NearleyRule[];
  ParserStart: string;
};

const grammar: Grammar = {
  Lexer: lexer,
  ParserRules: [
    {"name": "lines$ebnf$1", "symbols": []},
    {"name": "lines$ebnf$1", "symbols": ["lines$ebnf$1", "line"], "postprocess": (d) => d[0].concat([d[1]])},
    {"name": "lines", "symbols": ["lines$ebnf$1"], "postprocess": ([t]) => t},
    {"name": "line$ebnf$1", "symbols": []},
    {"name": "line$ebnf$1", "symbols": ["line$ebnf$1", "param"], "postprocess": (d) => d[0].concat([d[1]])},
    {"name": "line", "symbols": ["id", "line$ebnf$1", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", "e"], "postprocess": ([ id,params,,ty     ,e]) => Decl(e,id,params,ty           )},
    {"name": "line$ebnf$2", "symbols": []},
    {"name": "line$ebnf$2", "symbols": ["line$ebnf$2", "param"], "postprocess": (d) => d[0].concat([d[1]])},
    {"name": "line", "symbols": [(lexer.has("CMD_CONST") ? {type: "CMD_CONST"} : CMD_CONST), "id", "line$ebnf$2", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", "e"], "postprocess": ([,id,params,,ty     ,e]) => Decl(e,id,params,ty,null,'cst')},
    {"name": "line", "symbols": [(lexer.has("CMD_THM") ? {type: "CMD_THM"} : CMD_THM), "id", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", "e"], "postprocess": ([,id,       ,ty     ,e]) => Decl(e,id,[]    ,ty,null,'thm')},
    {"name": "line", "symbols": [(lexer.has("CMD_THM") ? {type: "CMD_THM"} : CMD_THM), "id", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("DEF") ? {type: "DEF"} : DEF), "term", "e"], "postprocess": ([,id,       ,ty,,def,e]) => Decl(e,id,[]    ,ty,def ,'thm')},
    {"name": "line$ebnf$3", "symbols": []},
    {"name": "line$ebnf$3", "symbols": ["line$ebnf$3", "param"], "postprocess": (d) => d[0].concat([d[1]])},
    {"name": "line", "symbols": ["id", "line$ebnf$3", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("DEF") ? {type: "DEF"} : DEF), "term", "e"], "postprocess": ([ id,params,,ty,,def,e]) => Decl(e,id,params,ty,def)},
    {"name": "line$ebnf$4", "symbols": []},
    {"name": "line$ebnf$4", "symbols": ["line$ebnf$4", "param"], "postprocess": (d) => d[0].concat([d[1]])},
    {"name": "line", "symbols": ["id", "line$ebnf$4", (lexer.has("DEF") ? {type: "DEF"} : DEF), "term", "e"], "postprocess": ([ id,params    ,,def,e]) => Decl(e,id,params,null,def)},
    {"name": "line", "symbols": [(lexer.has("CMD_CONST") ? {type: "CMD_CONST"} : CMD_CONST), "id", "e"], "postprocess": ([,id           ,e]) => DeclConst(e,id)},
    {"name": "line", "symbols": [(lexer.has("CMD_INJ") ? {type: "CMD_INJ"} : CMD_INJ), "id", "e"], "postprocess": ([,id           ,e]) => DeclInj(  e,id)},
    {"name": "line$ebnf$5", "symbols": ["id"], "postprocess": id},
    {"name": "line$ebnf$5", "symbols": [], "postprocess": () => null},
    {"name": "line", "symbols": ["line$ebnf$5", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("LONGARROW") ? {type: "LONGARROW"} : LONGARROW), "term", "e"], "postprocess": ([id,c,lhs,,rhs ,e]) => Rew(e,lhs,rhs,id || ('unnamed'+c.line)      )},
    {"name": "line$ebnf$6", "symbols": ["id"], "postprocess": id},
    {"name": "line$ebnf$6", "symbols": [], "postprocess": () => null},
    {"name": "line", "symbols": ["line$ebnf$6", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("LONGFATARROW") ? {type: "LONGFATARROW"} : LONGFATARROW), "term", "e"], "postprocess": ([id,c,lhs,,rhs ,e]) => Rew(e,lhs,rhs,id || ('unnamed'+c.line),false)},
    {"name": "line$ebnf$7", "symbols": ["alias"], "postprocess": id},
    {"name": "line$ebnf$7", "symbols": [], "postprocess": () => null},
    {"name": "line", "symbols": [(lexer.has("CMD_REQ") ? {type: "CMD_REQ"} : CMD_REQ), "id", "line$ebnf$7", "e"], "postprocess": ([, id,alias    ,e]) => CmdReq(e,id,alias)},
    {"name": "line$ebnf$8", "symbols": ["alias"], "postprocess": id},
    {"name": "line$ebnf$8", "symbols": [], "postprocess": () => null},
    {"name": "line", "symbols": [(lexer.has("CMD_REQ") ? {type: "CMD_REQ"} : CMD_REQ), "mid", "line$ebnf$8", "e"], "postprocess": ([,mid,alias    ,e]) => CmdReq(e,mid,alias)},
    {"name": "line", "symbols": [(lexer.has("CMD_EVAL") ? {type: "CMD_EVAL"} : CMD_EVAL), "ctxt", "term", "e"], "postprocess": ([,c,t          ,e]) => CmdEval(e,c,t)},
    {"name": "line", "symbols": [(lexer.has("CMD_INFER") ? {type: "CMD_INFER"} : CMD_INFER), "ctxt", "term", "e"], "postprocess": ([,c,t          ,e]) => CmdInfer(e,c,t)},
    {"name": "line", "symbols": [(lexer.has("CMD_CHECK") ? {type: "CMD_CHECK"} : CMD_CHECK), "ctxt", "aterm", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", "e"], "postprocess": ([,c,t,,ty      ,e]) => CmdCheckType(e,c,t,ty)},
    {"name": "line", "symbols": [(lexer.has("CMD_CHECK") ? {type: "CMD_CHECK"} : CMD_CHECK), "ctxt", "aterm", (lexer.has("CONV") ? {type: "CONV"} : CONV), "term", "e"], "postprocess": ([,c,t1,,t2     ,e]) => CmdCheckConv(e,c,t1,t2,true)},
    {"name": "line", "symbols": [(lexer.has("CMD_CHECK") ? {type: "CMD_CHECK"} : CMD_CHECK), "ctxt", "aterm", (lexer.has("NCONV") ? {type: "NCONV"} : NCONV), "term", "e"], "postprocess": ([,c,t1,,t2     ,e]) => CmdCheckConv(e,c,t1,t2,false)},
    {"name": "line", "symbols": [(lexer.has("CMD_PRINT") ? {type: "CMD_PRINT"} : CMD_PRINT), "term", "e"], "postprocess": ([,t            ,e]) => CmdPrint(e,t)},
    {"name": "line", "symbols": [(lexer.has("CMD_DTREE") ? {type: "CMD_DTREE"} : CMD_DTREE), "id", "e"], "postprocess": ([,id           ,e]) => CmdDTree(e,id)},
    {"name": "line", "symbols": [(lexer.has("CMD_TIME") ? {type: "CMD_TIME"} : CMD_TIME), "e"], "postprocess": ([              ,e]) => CmdTime(e)},
    {"name": "line", "symbols": [(lexer.has("CMD_DEBUGON") ? {type: "CMD_DEBUGON"} : CMD_DEBUGON), "e"], "postprocess": ([              ,e]) => CmdDebugOn(e)},
    {"name": "line", "symbols": [(lexer.has("CMD_DEBUGOFF") ? {type: "CMD_DEBUGOFF"} : CMD_DEBUGOFF), "e"], "postprocess": ([              ,e]) => CmdDebugOff(e)},
    {"name": "id", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID)], "postprocess": ([id ]) =>  id.value},
    {"name": "mid", "symbols": [(lexer.has("MID") ? {type: "MID"} : MID)], "postprocess": ([mid]) => mid.value.substring(1,mid.value.length-1)},
    {"name": "e", "symbols": [(lexer.has("END") ? {type: "END"} : END)], "postprocess": ([e  ]) =>   e.line},
    {"name": "alias", "symbols": [(lexer.has("LEFTSQU") ? {type: "LEFTSQU"} : LEFTSQU), "id", (lexer.has("RIGHTSQU") ? {type: "RIGHTSQU"} : RIGHTSQU)], "postprocess": ([,id,]) => id},
    {"name": "assign", "symbols": ["id", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term"], "postprocess": ([name,,type]) => [name,type]},
    {"name": "ctxt", "symbols": [], "postprocess": () => []},
    {"name": "ctxt", "symbols": [(lexer.has("ENT") ? {type: "ENT"} : ENT)], "postprocess": () => []},
    {"name": "ctxt$ebnf$1", "symbols": []},
    {"name": "ctxt$ebnf$1", "symbols": ["ctxt$ebnf$1", "_ctxt"], "postprocess": (d) => d[0].concat([d[1]])},
    {"name": "ctxt", "symbols": ["assign", "ctxt$ebnf$1", (lexer.has("ENT") ? {type: "ENT"} : ENT)], "postprocess": ([a,args]) => [a].concat(args)},
    {"name": "_ctxt", "symbols": [(lexer.has("COMMA") ? {type: "COMMA"} : COMMA), "assign"], "postprocess": ([,a]) => a},
    {"name": "param", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), "id", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR)], "postprocess": ([,v,,ty]) => [v,ty]},
    {"name": "args", "symbols": [], "postprocess": () => []},
    {"name": "args$ebnf$1", "symbols": []},
    {"name": "args$ebnf$1", "symbols": ["args$ebnf$1", "_args"], "postprocess": (d) => d[0].concat([d[1]])},
    {"name": "args", "symbols": ["term", "args$ebnf$1"], "postprocess": ([a,args]) => [a].concat(args)},
    {"name": "_args", "symbols": [(lexer.has("COMMA") ? {type: "COMMA"} : COMMA), "term"], "postprocess": ([,t]) => t},
    {"name": "sterm", "symbols": [(lexer.has("JOKER") ? {type: "JOKER"} : JOKER)], "postprocess": () => Joker()},
    {"name": "sterm", "symbols": [(lexer.has("TYPE") ? {type: "TYPE"} : TYPE)], "postprocess": () => Typ()},
    {"name": "sterm", "symbols": [(lexer.has("KIND") ? {type: "KIND"} : KIND)], "postprocess": () => Knd()},
    {"name": "sterm", "symbols": ["id", (lexer.has("LEFTSQU") ? {type: "LEFTSQU"} : LEFTSQU), "args", (lexer.has("RIGHTSQU") ? {type: "RIGHTSQU"} : RIGHTSQU)], "postprocess": ([id,,args]) => PMVar(id,args)},
    {"name": "sterm", "symbols": ["id"], "postprocess": ([id]) => PreScope(id)},
    {"name": "sterm", "symbols": [(lexer.has("QID") ? {type: "QID"} : QID)], "postprocess": ([id]) => PreRef(id.value)},
    {"name": "sterm", "symbols": [(lexer.has("DB_INDEX") ? {type: "DB_INDEX"} : DB_INDEX)], "postprocess": ([dbi]) => Var( parseInt(dbi.value.substring(1)) )},
    {"name": "sterm", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), "term", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR)], "postprocess": ([,t,]) => t},
    {"name": "aterm$ebnf$1", "symbols": []},
    {"name": "aterm$ebnf$1", "symbols": ["aterm$ebnf$1", "sterm"], "postprocess": (d) => d[0].concat([d[1]])},
    {"name": "aterm", "symbols": ["sterm", "aterm$ebnf$1"], "postprocess": ([te,ts]) => app(te,ts)},
    {"name": "term", "symbols": ["aterm"], "postprocess": ([t]) => t},
    {"name": "term", "symbols": ["id", (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("ARROW") ? {type: "ARROW"} : ARROW), "term"], "postprocess": ([ id,,dom,  ,cod ]) => PAll(id,dom,cod)},
    {"name": "term", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), "id", (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR), (lexer.has("ARROW") ? {type: "ARROW"} : ARROW), "term"], "postprocess": ([,id,,dom,, ,cod ]) => PAll(id,dom,cod)},
    {"name": "term", "symbols": ["aterm", (lexer.has("ARROW") ? {type: "ARROW"} : ARROW), "term"], "postprocess": ([     dom,  ,cod ]) => PAll(null,dom,cod)},
    {"name": "term", "symbols": ["id", (lexer.has("FATARROW") ? {type: "FATARROW"} : FATARROW), "term"], "postprocess": ([ id,       ,body]) => PLam(id,Joker(),body)},
    {"name": "term", "symbols": ["id", (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("FATARROW") ? {type: "FATARROW"} : FATARROW), "term"], "postprocess": ([ id,,type, ,body]) => PLam(id,type,body)},
    {"name": "term", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), "id", (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR), (lexer.has("FATARROW") ? {type: "FATARROW"} : FATARROW), "term"], "postprocess": ([,id,,type,,,body]) => PLam(id,type,body)},
    {"name": "term", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), "id", (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("DEF") ? {type: "DEF"} : DEF), "aterm", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR), (lexer.has("FATARROW") ? {type: "FATARROW"} : FATARROW), "term"], "postprocess": ([,id,,type,,val,,,body]) => PApp(Lam(id,type,body), val)}
  ],
  ParserStart: "lines",
};

export default grammar;
