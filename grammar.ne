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
    CMD_REQ  :"#REQUIRE",
    CMD_EVAL :"#EVAL",
    CMD_INFER:"#INFER",
    CMD_CHECK:"#CHECK",
    CMD_PRINT:"#PRINT",
    ID: /[a-zA-Z0-9_!?']+/,
  }, ['_','COMMENT']);

%}

# Pass your lexer object using the @lexer option:
@lexer lexer

lines -> line:* {% ([t]) => t %}

line ->
    %ID _:? param:* %COLON term       %END {% ([name,params,,ty,     ]) => Decl(name,params,ty) %}
  | %ID param:* %COLON term %DEF term %END {% ([name,params,,ty,,def,]) => Def(name,params,ty,def) %}
  | %ID:? %COLON term %LONGARROW term %END {% ([name,,lhs,,rhs,]) => Rew(lhs,rhs,name) %}
  | %CMD_REQ    %ID               %END {% ([,id])    => CmdReq(id)     %}
  | %CMD_EVAL   term              %END {% ([,t])     => CmdEval(t)     %}
  | %CMD_INFER  term              %END {% ([,t])     => CmdInfer(t)    %}
  | %CMD_CHECK  aterm %COLON term %END {% ([,t,,ty]) => CmdCheck(t,ty) %}
  | %CMD_PRINT  term              %END {% ([,t])     => CmdPrint(t)    %}

param -> %LEFTPAR %ID %COLON term %RIGHTPAR {% ([,v,,ty]) => [v,ty] %}

args  -> null {% () => [] %} | term _args:* {% ([a,args]) => [a]+args %}
_args -> %COMMA term {% ([,t]) => t %}

sterm ->
    %STAR                       {% () => Star() %}
  | %TYPE                       {% () => Typ()  %}
  | %ID %LEFTSQU args %RIGHTSQU {% ([name,,args]) => MVar(name,args) %}
  | %ID                         {% ([id]) => PreScope(id) %}
  | %LEFTPAR term %RIGHTPAR     {% ([,t,]) => t %}

aterm -> sterm sterm:* {% ([te,ts]) => app(te,ts) %}

term ->
    aterm                                           {% ([t]) => t %}
  | %ID %COLON aterm %ARROW term                    {% ([ name,,dom, ,cod]) => All(name,dom,cod) %}
  | %LEFTPAR %ID %COLON aterm %RIGHTPAR %ARROW term {% ([,name,,dom,,,cod]) => All(name,dom,cod) %}
  | aterm %ARROW term                               {% ([    dom, ,cod])    => All(null,dom,cod) %}
  | %ID %FATARROW term                              {% ([name,,body])       => Lam(name,Star(),body) %}
  | %ID %COLON aterm %FATARROW term                 {% ([name,,type,,body]) => Lam(name,type,body) %}
  | %LEFTPAR %ID %COLON aterm %DEF aterm %RIGHTPAR %FATARROW term
    {% ([,name,,type,,val,,,body]) => App(Lam(name,type,body), val) %}

# Whitespace
_ -> %WS:? {% function() {} %}
__ -> %WS  {% function() {} %}