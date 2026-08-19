:- module(main, [sol/2, sol/4]).


:- set_prolog_flag(answer_write_options, [quoted(true), portray(true), max_depth(0)]).
:- use_module('cnf.pro').
:- use_module('tokenize.pro').
:- use_module('sat_parse.pro').
:- use_module('quantum.pro').
:- use_module(library(janus)).

% initialize the python virtual environment inside of swipl
:- initialization((
    (  getenv('CONDA_PREFIX', CondaEnv)
    -> atomic_list_concat([CondaEnv, '/lib/python3.12/site-packages'], CondaSitePackages),
       py_call(sys:path:insert(0,CondaSitePackages))    
    ;  writeln('Warning: CONDA_PREFIX environment variable not found.')
    )
)).

% sol(S, A) is the convenience entry point used by the original tests:
% full preprocessing, metrics discarded. Equivalent to sol(S, full, A, _).
sol(S, A) :-
  sol(S, full, A, _).

% sol(S, Preprocess, A, Metrics)
%
% Preprocess is `full` (apply cnf.pro's optimize/2 pass: tautology removal,
% unit propagation, pure literal elimination) or `none` (skip it, to build
% the oracle from the original, unoptimized CNF for comparison).
%
% A is one of:
%   unsat        - classical preprocessing derived a contradiction (only possible with Preprocess = full; see cnf.pro)
%   tautology    - classical preprocessing derived the formula is always true (only possible with Preprocess = full; see cnf.pro)
%   sat(Assign)  - BBHT found and classically verified a satisfying assignment
%   unknown      - the BBHT iteration budget was exhausted without a verified assignment; this is NOT a proof of unsatisfiability
%
% Metrics = metrics(OracleMetrics, Attempts) as returned by quantum/3, or metrics(none, []) when the quantum module was never invoked (unsat/tautology).
sol(S, Preprocess, A, Metrics) :-
  tokenize(S, TOK),
  parse_sat(TOK, AST),
  cnfify(AST, Preprocess, CNF),
  ( CNF = unsat -> A = unsat, Metrics = metrics(none, [])
  ; CNF = sat   -> A = tautology, Metrics = metrics(none, [])
  ;               quantum(CNF, A, Metrics)).

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