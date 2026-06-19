:- module(quantum, [quantum/2]).

:- use_module(library(janus)).

quantum(CNF, A) :- 
  py_call(pymain:oracle(CNF), Oracle-Vars),
  length(CNF, NClauses),
  length(Vars, NVar),
  Bound is ceiling(sqrt(2 ** NVar)),
  run_grover(CNF, Oracle, Vars, NVar, NClauses, 1, Bound, A).

run_grover(CNF, Oracle, Vars, NVar, NClauses, Iters, Bound, A) :-
  format("Running grover with ~d~n", [Iters]),
  ( Iters > Bound -> A = contradiction
  ;  py_call(pymain:run_grover(Oracle, NVar, NClauses, Iters), R),
    ( verify(CNF, Vars, R, VR), VR = [_|_] -> assignment(VR, Vars, A)
    ; NewIters is min(ceiling(Iters * 3 / 2), Bound),
      ( NewIters > Iters -> run_grover(CNF, Oracle, Vars, NVar, NClauses, NewIters, Bound, A)
      ; A = contradiction
      )
    )
  ).

verify(_CNF, _Vars, [], []).
verify(CNF, Vars, [S|T], V) :-
  ( satisfies(CNF, Vars, S) -> V = [S|R]
  ; V = R 
  ),
  verify(CNF, Vars, T, R).

satisfies(CNF, Vars, S) :-
  ( string(S) -> string_chars(S, C) ; atom_chars(S, C) ),
  reverse(C, R),
  pairs_keys_values(P, Vars, R),
  eval_cnf(CNF, P).

eval_cnf([], _).
eval_cnf([N-S|T], A) :-
  ((member(V, S), member(V-'1', A)) ; (member(V, N), member(V-'0', A))),
  eval_cnf(T, A).

assignment([], _, []).
assignment([V|Vs], Vars, [F-T|Rest]) :-
  ( string(V) -> string_chars(V, C) ; atom_chars(V, C) ),
  reverse(C, R),
  pairs_keys_values(P, Vars, R),
  partition(is_true, P, TP, FP),
  pairs_keys(TP, T),
  pairs_keys(FP, F),
  assignment(Vs, Vars,Rest).

is_true(_-'1').