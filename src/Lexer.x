{
module Lexer where
import Data.Char (ord)
}

%wrapper "basic"

$upper = [A-Z]
$eol = [\n]

tokens :-
       $eol                        ;
       $white+                     ;
       "⇒"                         { \_ -> ARROW }
       "("                         { \_ -> LPAREN }
       ")"                         { \_ -> RPAREN }
       $upper                      { \s -> VAR $ ord $ head s }

{
data Token = ARROW
           | LPAREN
           | RPAREN
           | VAR Int
           deriving(Eq, Show)

scanTokens = alexScanTokens
}