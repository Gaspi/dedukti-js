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
    DEF     :':=',
    CONV    :'==',
    COLON   :':',
    LEFTSQU :'[',
    RIGHTSQU:']',
    LEFTBRA :'{',
    RIGHTBRA:'}',
    LEFTPAR :'(',
    RIGHTPAR:')',
    STAR    :'*',
    END     :';',
    ARROW   :'->',
    FATARROW:'=>',
    LONGARROW:'-->',
    TYPE:"Type",
    KIND:"Kind",
    CMD_REQ  :"#REQUIRE",
    CMD_EVAL :"#EVAL",
    CMD_INFER:"#INFER",
    CMD_CHECK:"#CHECK",
    CMD_PRINT:"#PRINT",
    QID: /(?:[a-zA-Z0-9_']+\.)+[a-zA-Z0-9_\-!?']+/,
    ID: /[a-zA-Z0-9_!?']+/,
  }, ['_','COMMENT']);

%}

# Pass your lexer object using the @lexer option:
@lexer lexer

lines -> line:* {% ([t]) => t %}

line ->
    %ID param:* %COLON term                 %END {% ([id,params,,ty,     ]) => Decl(id.value,params,ty) %}
  | %ID param:* %COLON term %DEF term       %END {% ([id,params,,ty,,def,]) => Def(id.value,params,ty,def) %}
  | %ID:? %COLON term %LONGARROW term       %END {% ([id,c,lhs,,rhs,])      => Rew(lhs,rhs, id?id.value:'unnamed'+c.line) %}
  | %CMD_REQ    %ID                         %END {% ([,id])         => CmdReq(id)          %}
  | %CMD_REQ    %QID %LEFTSQU %ID %RIGHTSQU %END {% ([,id,,alias,]) => CmdReq(id,alias)    %}
  | %CMD_EVAL   term                        %END {% ([,t])          => CmdEval(t)          %}
  | %CMD_INFER  term                        %END {% ([,t])          => CmdInfer(t)         %}
  | %CMD_CHECK  aterm %COLON term           %END {% ([,t,,ty])      => CmdCheckType(t,ty)  %}
  | %CMD_CHECK  aterm %CONV term            %END {% ([,t1,,t2])     => CmdCheckConv(t1,t2) %}
  | %CMD_PRINT  term                        %END {% ([,t])          => CmdPrint(t)         %}

param -> %LEFTPAR %ID %COLON term %RIGHTPAR {% ([,v,,ty]) => [v,ty] %}

args  -> null {% () => [] %} | term _args:* {% ([a,args]) => [a].concat(args) %}
_args -> %COMMA term {% ([,t]) => t %}

qid -> %ID _qid:* {% ([a,args]) => [a.value].concat(args).join('.') %}
_qid -> %DOT %ID {% ([,t]) => t.value %}

sterm ->
    %STAR                       {% () => Star() %}
  | %TYPE                       {% () => Typ()  %}
  | %KIND                       {% () => Knd()  %}
  | %ID %LEFTSQU args %RIGHTSQU {% ([id,,args]) => MVar(id.value,args) %}
  | %ID                         {% ([id]) => PreScope(id.value) %}
  | %QID                        {% ([id]) => PreRef(id.value) %}
  | %LEFTPAR term %RIGHTPAR     {% ([,t,]) => t %}

aterm -> sterm sterm:* {% ([te,ts]) => app(te,ts) %}

term ->
    aterm                                              {% ([t]) => t %}
  | %ID %COLON aterm %ARROW term                       {% ([ id,,dom, ,cod]) => All(id.value,dom,cod) %}
  | %LEFTPAR %ID %COLON aterm %RIGHTPAR %ARROW term    {% ([,id,,dom,,,cod]) => All(id.value,dom,cod) %}
  | aterm %ARROW term                                  {% ([     dom, ,cod]) => All(null,dom,cod) %}
  | %ID %FATARROW term                                 {% ([id,,body])       => Lam(id.value,Star(),body) %}
  | %ID %COLON aterm %FATARROW term                    {% ([id,,type,,body]) => Lam(id.value,type,body) %}
  | %LEFTPAR %ID %COLON aterm %RIGHTPAR %FATARROW term {% ([,id,,type,,,body]) => Lam(id.value,type,body) %}
  | %LEFTPAR %ID %COLON aterm %DEF aterm %RIGHTPAR %FATARROW term
    {% ([,id,,type,,val,,,body]) => App(Lam(id.value,type,body), val) %}
