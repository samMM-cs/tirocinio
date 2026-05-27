:- set_prolog_flag(answer_write_options, [quoted(true), portray(true), max_depth(0)]).
:- use_module('cnf.pro').
:- use_module('tokenize.pro').
:- use_module('sat_parse.pro').
:- use_module(library(janus)).

sol(S, A) :-
  tokenize(S, TOK),
  parse_sat(TOK, AST),
  cnfify(AST, CNF),
  ( CNF = unsat -> A = contradiction
  ; CNF = sat   -> A = tautology
  ;               quantum(CNF, A)).

quantum(CNF, CNF) :- 
  py_call(pymain:main(CNF)).
% cerca iterazioni random, oppure incrementale, oppure binary search

% [([1,2,3], [4,5])]

test_expr(0, "(!A || B || C) && (A || !C) && (!B)").
test_expr(1, "A && (B || ~C)").
test_expr(2, "P and NOT P").
test_expr(3, "(A => B) && A && !B").
test_expr(4, "(A -> B) and (B -> C) and (A and !C)").
test_expr(5, "(NOT (A AND B)) <=> ((NOT A) OR (NOT B))").
test_expr(6, "(A ^ B) <-> ((A and !B) or (!A and B))").
test_expr(7, "((X || Y) && (X -> Z) && (Y -> Z)) => Z").
test_expr(8, "(A | B) & (!A | B) & (A | !B) & (!A | !B)").
test_expr(9, "A xor B xor C xor (A && B && C)").