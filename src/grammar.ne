@{%

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
    DB_INDEX:/\#[0-9]+/,
    MID: /"[^"]*"/,
    QID: /(?:[a-zA-Z0-9_!?'/]+\.)+[a-zA-Z0-9_!?'/]+/,
    ID: /[a-zA-Z0-9_!?'/]+/,
  }, ['_','COMMENT']);

%}

# Pass your lexer object using the @lexer option:
@lexer lexer

lines -> line:* {% ([t]) => t %}

line ->
               %ID param:* %COLON term   %END {% ([ id,params,,ty,e]) => Decl(     e.line,id.value,params,ty)   %}
  | %CMD_CONST %ID param:* %COLON term   %END {% ([,id,params,,ty,e]) => DeclConst(e.line,id.value,params,ty)   %}
  | %CMD_THM   %ID %COLON term           %END {% ([,id,,ty       ,e]) => Thm(e.line,id.value,ty)                %}
  | %CMD_THM   %ID %COLON term %DEF term %END {% ([,id,,ty,,def  ,e]) => Thm(e.line,id.value,ty,def)            %}
  | %CMD_CONST %ID                       %END {% ([,id           ,e]) => DeclConstP(e.line,id.value)            %}
  | %CMD_INJ   %ID                       %END {% ([,id           ,e]) => DeclInj(e.line,id.value)               %}
  | %ID param:* %COLON term %DEF term    %END {% ([id,params,,ty,,def,e]) => Def(e.line,id.value,params,ty,def) %}
  | %ID:? %COLON term %LONGARROW    term %END {% ([id,c,lhs,,rhs ,e]) => Rew(e.line,lhs,rhs,id?id.value:'unnamed'+c.line      ) %}
  | %ID:? %COLON term %LONGFATARROW term %END {% ([id,c,lhs,,rhs ,e]) => Rew(e.line,lhs,rhs,id?id.value:'unnamed'+c.line,false) %}
  | %CMD_REQ    %ID  alias:?             %END {% ([, id,alias    ,e]) => CmdReq(e.line, id.value,alias)         %}
  | %CMD_REQ    %MID alias:?             %END {% ([,mid,alias    ,e]) => CmdReq(e.line,mid.value.substring(1,mid.value.length-1),alias)%}
  | %CMD_EVAL  ctxt term                 %END {% ([,c,t          ,e]) => CmdEval(e.line,c,t)                    %}
  | %CMD_INFER ctxt term                 %END {% ([,c,t          ,e]) => CmdInfer(e.line,c,t)                   %}
  | %CMD_CHECK ctxt aterm %COLON term    %END {% ([,c,t,,ty      ,e]) => CmdCheckType(e.line,c,t,ty)            %}
  | %CMD_CHECK ctxt aterm  %CONV term    %END {% ([,c,t1,,t2     ,e]) => CmdCheckConv(e.line,c,t1,t2,true)      %}
  | %CMD_CHECK ctxt aterm %NCONV term    %END {% ([,c,t1,,t2     ,e]) => CmdCheckConv(e.line,c,t1,t2,false)     %}
  | %CMD_PRINT  term                     %END {% ([,t            ,e]) => CmdPrint(e.line,t)                     %}
  | %CMD_DTREE %ID                       %END {% ([,id           ,e]) => CmdDTree(e.line,id.value)              %}
  | %CMD_TIME                            %END {% ([              ,e]) => CmdTime(e.line)                        %}

alias -> %LEFTSQU %ID %RIGHTSQU {% ([,id,]) => id.value %}
assign -> %ID %COLON term {% ([name,,type]) => [name.value,type] %}

ctxt -> null {% () => [] %} | %ENT {% () => [] %} | assign _ctxt:* %ENT {% ([a,args]) => [a].concat(args) %}
_ctxt -> %COMMA assign {% ([,a]) => a %}

param -> %LEFTPAR %ID %COLON term %RIGHTPAR {% ([,v,,ty]) => [v.value,ty] %}

args  -> null {% () => [] %} | term _args:* {% ([a,args]) => [a].concat(args) %}
_args -> %COMMA term {% ([,t]) => t %}

qid -> %ID _qid:* {% ([a,args]) => [a.value].concat(args).join('.') %}
_qid -> %DOT %ID {% ([,t]) => t.value %}

sterm ->
    %JOKER                      {% () => Joker() %}
  | %TYPE                       {% () => Typ()  %}
  | %KIND                       {% () => Knd()  %}
  | %ID %LEFTSQU args %RIGHTSQU {% ([id,,args]) => MVar(id.value,args) %}
  | %ID                         {% ([id]) => PreScope(id.value) %}
  | %QID                        {% ([id]) => PreRef(id.value) %}
  | %DB_INDEX                   {% ([dbi]) => Var( parseInt(dbi.value.substring(1)) ) %}
  | %LEFTPAR term %RIGHTPAR     {% ([,t,]) => t %}

aterm -> sterm sterm:* {% ([te,ts]) => app(te,ts) %}

term ->
    aterm                                              {% ([t]) => t %}
  | %ID %COLON aterm %ARROW term                       {% ([ id,,dom, ,cod]) => All(id.value,dom,cod) %}
  | %LEFTPAR %ID %COLON aterm %RIGHTPAR %ARROW term    {% ([,id,,dom,,,cod]) => All(id.value,dom,cod) %}
  | aterm %ARROW term                                  {% ([     dom, ,cod]) => All(null,dom,cod) %}
  | %ID %FATARROW term                                 {% ([id,,body])       => Lam(id.value,Joker(),body) %}
  | %ID %COLON aterm %FATARROW term                    {% ([id,,type,,body]) => Lam(id.value,type,body) %}
  | %LEFTPAR %ID %COLON aterm %RIGHTPAR %FATARROW term {% ([,id,,type,,,body]) => Lam(id.value,type,body) %}
  | %LEFTPAR %ID %COLON aterm %DEF aterm %RIGHTPAR %FATARROW term
    {% ([,id,,type,,val,,,body]) => App(Lam(id.value,type,body), val) %}
