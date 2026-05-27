:- module(sat_parse, [parse_sat/2]).

:- use_module('tokenize.pro').

parse_sat(S, AST) :- phrase(expression(AST), S).

% Axiom of the grammar, captures lowest precedence
expression(implies(A, B)) --> term_or(A), [OP], {bool_op(OP, impl)}, expression(B).
expression(equiv(A, B)) --> term_or(A), [OP], {bool_op(OP, equiv)}, expression(B).
expression(A) --> term_or(A).

% OR, 2nd lowest
term_or(or(A, B)) --> term_xor(A), [OP], {bool_op(OP, or)}, term_or(B).
term_or(A) --> term_xor(A).

% XOR, 3rd lowest
term_xor(xor(A, B)) --> term_and(A), [OP], {bool_op(OP, xor)}, term_xor(B).
term_xor(A) --> term_and(A).

% AND, 3rd highest
term_and(and(A, B)) --> term_not(A), [OP], {bool_op(OP, and)}, term_and(B).
term_and(A) --> term_not(A).

% NOT, 2nd highest
term_not(not(A)) --> [OP], {bool_op(OP, not)}, term_not(A).
term_not(A) --> factor(A).

% factors, highest
factor(A) --> ['('], expression(A), [')'].
factor(var(X)) --> [var(X)].
