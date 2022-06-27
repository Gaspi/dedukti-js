// Generated automatically by nearley, version 2.20.1
// http://github.com/Hardmath123/nearley
(function () {
function id(x) { return x[0]; }


function makeLexer(tokens, ignoreTokens) {
  let lexer = moo.compile(tokens);
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
  lexer.ignoreSet = new Set(ignoreTokens);
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
    STAR    :'*',
    END     :';',
    TYPE:"Type",
    KIND:"Kind",
    CMD_REQ  :"#REQUIRE",
    CMD_EVAL :"#EVAL",
    CMD_INFER:"#INFER",
    CMD_CHECK:"#CHECK",
    CMD_CONST:"#CONST",
    CMD_INJ  :"#INJECTIVE",
    CMD_PRINT:"#PRINT",
    CMD_DTREE:"#DTREE",
    DB_INDEX:/\#[0-9]+/,
    MID: /"[^"]*"/,
    QID: /(?:[a-zA-Z0-9_!?'/]+\.)+[a-zA-Z0-9_!?'/]+/,
    ID: /[a-zA-Z0-9_!?'/]+/,
  }, ['_','COMMENT']);

var grammar = {
    Lexer: lexer,
    ParserRules: [
    {"name": "lines$ebnf$1", "symbols": []},
    {"name": "lines$ebnf$1", "symbols": ["lines$ebnf$1", "line"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "lines", "symbols": ["lines$ebnf$1"], "postprocess": ([t]) => t},
    {"name": "line$ebnf$1", "symbols": []},
    {"name": "line$ebnf$1", "symbols": ["line$ebnf$1", "param"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "line", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID), "line$ebnf$1", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([ id,params,,ty,e]) => Decl(     e.line,id.value,params,ty)},
    {"name": "line$ebnf$2", "symbols": []},
    {"name": "line$ebnf$2", "symbols": ["line$ebnf$2", "param"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "line", "symbols": [(lexer.has("CMD_CONST") ? {type: "CMD_CONST"} : CMD_CONST), (lexer.has("ID") ? {type: "ID"} : ID), "line$ebnf$2", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,id,params,,ty,e]) => DeclConst(e.line,id.value,params,ty)},
    {"name": "line", "symbols": [(lexer.has("CMD_CONST") ? {type: "CMD_CONST"} : CMD_CONST), (lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,id           ,e]) => DeclConstP(e.line,id.value)},
    {"name": "line", "symbols": [(lexer.has("CMD_INJ") ? {type: "CMD_INJ"} : CMD_INJ), (lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,id           ,e]) => DeclInj(e.line,id.value)},
    {"name": "line$ebnf$3", "symbols": []},
    {"name": "line$ebnf$3", "symbols": ["line$ebnf$3", "param"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "line", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID), "line$ebnf$3", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("DEF") ? {type: "DEF"} : DEF), "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([id,params,,ty,,def,e]) => Def(e.line,id.value,params,ty,def)},
    {"name": "line$ebnf$4", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID)], "postprocess": id},
    {"name": "line$ebnf$4", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "line", "symbols": ["line$ebnf$4", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("LONGARROW") ? {type: "LONGARROW"} : LONGARROW), "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([id,c,lhs,,rhs ,e]) => Rew(e.line,lhs,rhs,id?id.value:'unnamed'+c.line      )},
    {"name": "line$ebnf$5", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID)], "postprocess": id},
    {"name": "line$ebnf$5", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "line", "symbols": ["line$ebnf$5", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("LONGFATARROW") ? {type: "LONGFATARROW"} : LONGFATARROW), "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([id,c,lhs,,rhs ,e]) => Rew(e.line,lhs,rhs,id?id.value:'unnamed'+c.line,false)},
    {"name": "line$ebnf$6", "symbols": ["alias"], "postprocess": id},
    {"name": "line$ebnf$6", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "line", "symbols": [(lexer.has("CMD_REQ") ? {type: "CMD_REQ"} : CMD_REQ), (lexer.has("ID") ? {type: "ID"} : ID), "line$ebnf$6", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([, id,alias    ,e]) => CmdReq(e.line, id.value,alias)},
    {"name": "line$ebnf$7", "symbols": ["alias"], "postprocess": id},
    {"name": "line$ebnf$7", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "line", "symbols": [(lexer.has("CMD_REQ") ? {type: "CMD_REQ"} : CMD_REQ), (lexer.has("MID") ? {type: "MID"} : MID), "line$ebnf$7", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,mid,alias    ,e]) => CmdReq(e.line,mid.value.substring(1,mid.value.length-1),alias)},
    {"name": "line", "symbols": [(lexer.has("CMD_EVAL") ? {type: "CMD_EVAL"} : CMD_EVAL), "ctxt", "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,c,t          ,e]) => CmdEval(e.line,c,t)},
    {"name": "line", "symbols": [(lexer.has("CMD_INFER") ? {type: "CMD_INFER"} : CMD_INFER), "ctxt", "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,c,t          ,e]) => CmdInfer(e.line,c,t)},
    {"name": "line", "symbols": [(lexer.has("CMD_CHECK") ? {type: "CMD_CHECK"} : CMD_CHECK), "ctxt", "aterm", (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,c,t,,ty      ,e]) => CmdCheckType(e.line,c,t,ty)},
    {"name": "line", "symbols": [(lexer.has("CMD_CHECK") ? {type: "CMD_CHECK"} : CMD_CHECK), "ctxt", "aterm", (lexer.has("CONV") ? {type: "CONV"} : CONV), "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,c,t1,,t2     ,e]) => CmdCheckConv(e.line,c,t1,t2,true)},
    {"name": "line", "symbols": [(lexer.has("CMD_CHECK") ? {type: "CMD_CHECK"} : CMD_CHECK), "ctxt", "aterm", (lexer.has("NCONV") ? {type: "NCONV"} : NCONV), "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,c,t1,,t2     ,e]) => CmdCheckConv(e.line,c,t1,t2,false)},
    {"name": "line", "symbols": [(lexer.has("CMD_PRINT") ? {type: "CMD_PRINT"} : CMD_PRINT), "term", (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,t            ,e]) => CmdPrint(e.line,t)},
    {"name": "line", "symbols": [(lexer.has("CMD_DTREE") ? {type: "CMD_DTREE"} : CMD_DTREE), (lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("END") ? {type: "END"} : END)], "postprocess": ([,id           ,e]) => CmdDTree(e.line,id.value)},
    {"name": "alias", "symbols": [(lexer.has("LEFTSQU") ? {type: "LEFTSQU"} : LEFTSQU), (lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("RIGHTSQU") ? {type: "RIGHTSQU"} : RIGHTSQU)], "postprocess": ([,id,]) => id.value},
    {"name": "assign", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("COLON") ? {type: "COLON"} : COLON), "term"], "postprocess": ([name,,type]) => [name.value,type]},
    {"name": "ctxt", "symbols": [], "postprocess": () => []},
    {"name": "ctxt", "symbols": [(lexer.has("ENT") ? {type: "ENT"} : ENT)], "postprocess": () => []},
    {"name": "ctxt$ebnf$1", "symbols": []},
    {"name": "ctxt$ebnf$1", "symbols": ["ctxt$ebnf$1", "_ctxt"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "ctxt", "symbols": ["assign", "ctxt$ebnf$1", (lexer.has("ENT") ? {type: "ENT"} : ENT)], "postprocess": ([a,args]) => [a].concat(args)},
    {"name": "_ctxt", "symbols": [(lexer.has("COMMA") ? {type: "COMMA"} : COMMA), "assign"], "postprocess": ([,a]) => a},
    {"name": "param", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), (lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("COLON") ? {type: "COLON"} : COLON), "term", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR)], "postprocess": ([,v,,ty]) => [v.value,ty]},
    {"name": "args", "symbols": [], "postprocess": () => []},
    {"name": "args$ebnf$1", "symbols": []},
    {"name": "args$ebnf$1", "symbols": ["args$ebnf$1", "_args"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "args", "symbols": ["term", "args$ebnf$1"], "postprocess": ([a,args]) => [a].concat(args)},
    {"name": "_args", "symbols": [(lexer.has("COMMA") ? {type: "COMMA"} : COMMA), "term"], "postprocess": ([,t]) => t},
    {"name": "qid$ebnf$1", "symbols": []},
    {"name": "qid$ebnf$1", "symbols": ["qid$ebnf$1", "_qid"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "qid", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID), "qid$ebnf$1"], "postprocess": ([a,args]) => [a.value].concat(args).join('.')},
    {"name": "_qid", "symbols": [(lexer.has("DOT") ? {type: "DOT"} : DOT), (lexer.has("ID") ? {type: "ID"} : ID)], "postprocess": ([,t]) => t.value},
    {"name": "sterm", "symbols": [(lexer.has("STAR") ? {type: "STAR"} : STAR)], "postprocess": () => Star()},
    {"name": "sterm", "symbols": [(lexer.has("TYPE") ? {type: "TYPE"} : TYPE)], "postprocess": () => Typ()},
    {"name": "sterm", "symbols": [(lexer.has("KIND") ? {type: "KIND"} : KIND)], "postprocess": () => Knd()},
    {"name": "sterm", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("LEFTSQU") ? {type: "LEFTSQU"} : LEFTSQU), "args", (lexer.has("RIGHTSQU") ? {type: "RIGHTSQU"} : RIGHTSQU)], "postprocess": ([id,,args]) => MVar(id.value,args)},
    {"name": "sterm", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID)], "postprocess": ([id]) => PreScope(id.value)},
    {"name": "sterm", "symbols": [(lexer.has("QID") ? {type: "QID"} : QID)], "postprocess": ([id]) => PreRef(id.value)},
    {"name": "sterm", "symbols": [(lexer.has("DB_INDEX") ? {type: "DB_INDEX"} : DB_INDEX)], "postprocess": ([dbi]) => Var( parseInt(dbi.value.substring(1)) )},
    {"name": "sterm", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), "term", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR)], "postprocess": ([,t,]) => t},
    {"name": "aterm$ebnf$1", "symbols": []},
    {"name": "aterm$ebnf$1", "symbols": ["aterm$ebnf$1", "sterm"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "aterm", "symbols": ["sterm", "aterm$ebnf$1"], "postprocess": ([te,ts]) => app(te,ts)},
    {"name": "term", "symbols": ["aterm"], "postprocess": ([t]) => t},
    {"name": "term", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("ARROW") ? {type: "ARROW"} : ARROW), "term"], "postprocess": ([ id,,dom, ,cod]) => All(id.value,dom,cod)},
    {"name": "term", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), (lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR), (lexer.has("ARROW") ? {type: "ARROW"} : ARROW), "term"], "postprocess": ([,id,,dom,,,cod]) => All(id.value,dom,cod)},
    {"name": "term", "symbols": ["aterm", (lexer.has("ARROW") ? {type: "ARROW"} : ARROW), "term"], "postprocess": ([     dom, ,cod]) => All(null,dom,cod)},
    {"name": "term", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("FATARROW") ? {type: "FATARROW"} : FATARROW), "term"], "postprocess": ([id,,body])       => Lam(id.value,Star(),body)},
    {"name": "term", "symbols": [(lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("FATARROW") ? {type: "FATARROW"} : FATARROW), "term"], "postprocess": ([id,,type,,body]) => Lam(id.value,type,body)},
    {"name": "term", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), (lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR), (lexer.has("FATARROW") ? {type: "FATARROW"} : FATARROW), "term"], "postprocess": ([,id,,type,,,body]) => Lam(id.value,type,body)},
    {"name": "term", "symbols": [(lexer.has("LEFTPAR") ? {type: "LEFTPAR"} : LEFTPAR), (lexer.has("ID") ? {type: "ID"} : ID), (lexer.has("COLON") ? {type: "COLON"} : COLON), "aterm", (lexer.has("DEF") ? {type: "DEF"} : DEF), "aterm", (lexer.has("RIGHTPAR") ? {type: "RIGHTPAR"} : RIGHTPAR), (lexer.has("FATARROW") ? {type: "FATARROW"} : FATARROW), "term"], "postprocess": ([,id,,type,,val,,,body]) => App(Lam(id.value,type,body), val)}
]
  , ParserStart: "lines"
}
if (typeof module !== 'undefined'&& typeof module.exports !== 'undefined') {
   module.exports = grammar;
} else {
   window.grammar = grammar;
}
})();
