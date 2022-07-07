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
    QID: /(?:[a-zA-Z0-9_!?'/@]+\.)+[a-zA-Z0-9_!?'/@]+/,
    ID: /[a-zA-Z0-9_!?'/@]+/,
  }, ['_','COMMENT']);

%}

# Pass your lexer object using the @lexer option:
@lexer lexer

lines -> line:* {% ([t]) => t %}

line ->
               id param:* %COLON term           e {% ([ id,params,,ty     ,e]) => Decl(e,id,params,ty           ) %}
  | %CMD_CONST id param:* %COLON term           e {% ([,id,params,,ty     ,e]) => Decl(e,id,params,ty,null,'cst') %}
  | %CMD_THM   id         %COLON term           e {% ([,id,       ,ty     ,e]) => Decl(e,id,[]    ,ty,null,'thm') %}
  | %CMD_THM   id         %COLON term %DEF term e {% ([,id,       ,ty,,def,e]) => Decl(e,id,[]    ,ty,def ,'thm') %}
  |            id param:* %COLON term %DEF term e {% ([ id,params,,ty,,def,e]) => Decl(e,id,params,ty,def)        %}
  |            id param:*             %DEF term e {% ([ id,params    ,,def,e]) => Decl(e,id,params,null,def)      %}
  | %CMD_CONST id                               e {% ([,id           ,e]) => DeclConst(e,id)                   %}
  | %CMD_INJ   id                               e {% ([,id           ,e]) => DeclInj(  e,id)                   %}
  | id:? %COLON term %LONGARROW    term         e {% ([id,c,lhs,,rhs ,e]) => Rew(e,lhs,rhs,id || ('unnamed'+c.line)      ) %}
  | id:? %COLON term %LONGFATARROW term         e {% ([id,c,lhs,,rhs ,e]) => Rew(e,lhs,rhs,id || ('unnamed'+c.line),false) %}
  | %CMD_REQ    id  alias:?                     e {% ([, id,alias    ,e]) => CmdReq(e,id,alias)                %}
  | %CMD_REQ    mid alias:?                     e {% ([,mid,alias    ,e]) => CmdReq(e,mid,alias)%}
  | %CMD_EVAL  ctxt term                        e {% ([,c,t          ,e]) => CmdEval(e,c,t)                    %}
  | %CMD_INFER ctxt term                        e {% ([,c,t          ,e]) => CmdInfer(e,c,t)                   %}
  | %CMD_CHECK ctxt aterm %COLON term           e {% ([,c,t,,ty      ,e]) => CmdCheckType(e,c,t,ty)            %}
  | %CMD_CHECK ctxt aterm  %CONV term           e {% ([,c,t1,,t2     ,e]) => CmdCheckConv(e,c,t1,t2,true)      %}
  | %CMD_CHECK ctxt aterm %NCONV term           e {% ([,c,t1,,t2     ,e]) => CmdCheckConv(e,c,t1,t2,false)     %}
  | %CMD_PRINT  term                            e {% ([,t            ,e]) => CmdPrint(e,t)                     %}
  | %CMD_DTREE id                               e {% ([,id           ,e]) => CmdDTree(e,id)                    %}
  | %CMD_TIME                                   e {% ([              ,e]) => CmdTime(e)                        %}

id  -> %ID  {% ([id ]) =>  id.value %}
mid -> %MID {% ([mid]) => mid.value.substring(1,mid.value.length-1)  %}
e   -> %END {% ([e  ]) =>   e.line  %}
alias -> %LEFTSQU id %RIGHTSQU {% ([,id,]) => id %}
assign -> id %COLON term {% ([name,,type]) => [name,type] %}

ctxt -> null            {% () => [] %}
  | %ENT                {% () => [] %}
  | assign _ctxt:* %ENT {% ([a,args]) => [a].concat(args) %}
_ctxt -> %COMMA assign {% ([,a]) => a %}

param -> %LEFTPAR id %COLON term %RIGHTPAR {% ([,v,,ty]) => [v,ty] %}

args  -> null {% () => [] %} | term _args:* {% ([a,args]) => [a].concat(args) %}
_args -> %COMMA term {% ([,t]) => t %}

sterm ->
    %JOKER                      {% () => Joker() %}
  | %TYPE                       {% () => Typ()  %}
  | %KIND                       {% () => Knd()  %}
  | id %LEFTSQU args %RIGHTSQU {% ([id,,args]) => MVar(id,args) %}
  | id                         {% ([id]) => PreScope(id) %}
  | %QID                        {% ([id]) => PreRef(id.value) %}
  | %DB_INDEX                   {% ([dbi]) => Var( parseInt(dbi.value.substring(1)) ) %}
  | %LEFTPAR term %RIGHTPAR     {% ([,t,]) => t %}

aterm -> sterm sterm:* {% ([te,ts]) => app(te,ts) %}

term ->
    aterm                                             {% ([t]) => t %}
  | id %COLON aterm %ARROW term                       {% ([ id,,dom,  ,cod ]) => All(id,dom,cod)      %}
  | %LEFTPAR id %COLON aterm %RIGHTPAR %ARROW term    {% ([,id,,dom,, ,cod ]) => All(id,dom,cod)      %}
  | aterm %ARROW term                                 {% ([     dom,  ,cod ]) => All(null,dom,cod)    %}
  | id              %FATARROW term                    {% ([ id,       ,body]) => Lam(id,Joker(),body) %}
  | id %COLON aterm %FATARROW term                    {% ([ id,,type, ,body]) => Lam(id,type,body)    %}
  | %LEFTPAR id %COLON aterm %RIGHTPAR %FATARROW term {% ([,id,,type,,,body]) => Lam(id,type,body)    %}
  | %LEFTPAR id %COLON aterm %DEF aterm %RIGHTPAR %FATARROW term
    {% ([,id,,type,,val,,,body]) => App(Lam(id,type,body), val) %}
