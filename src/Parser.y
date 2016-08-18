{
module Parser where

import Lexer
import Core
}

%name expr
%tokentype { Token }
%error { parseError }

%token
    '=>'     { ARROW }
    '('      { LPAREN }
    ')'      { RPAREN }
    var      { VAR $$ }

%%

Formula : Atom                  { $1 }
        | Formula '=>' Formula  { Imp $1 $3 }

Atom : var                      { Var $1 }
     | '(' Formula ')'          { $2 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"

parseExpr :: String -> Formula
parseExpr = expr . scanTokens
}