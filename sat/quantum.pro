:- module(quantum, [quantum/3, python_error_string/2]).

:- use_module(library(janus)).

% quantum(+CNF, -A, -Metrics)
%
% A is `sat(Assignment)` if BBHT found and classically verified a satisfying
% assignment, or `unknown` if the iteration budget was exhausted without one
% (this is NOT a proof of unsatisfiability).
%
% Metrics = metrics(OracleMetrics, Attempts):
%   OracleMetrics = oracle_metrics(NVars, NClauses, NQubits, NAncillas,
%                                   MCXCount, Depth, GateCounts, BuildTime)
%   Attempts      = list of attempt_metrics(IterationsUsed, MaxIterations,
%                                            SimTime, Shots, Counts),
%                   one entry per Grover call, oldest first.
quantum(CNF, A, metrics(OracleMetrics, Attempts)) :-
  py_call(pymain:oracle(CNF), -(Oracle, Vars, PyOracleMetrics)),
  oracle_metrics_term(PyOracleMetrics, OracleMetrics),
  length(CNF, NClauses),
  length(Vars, NVar),
  Bound is ceiling(sqrt(2 ** NVar)),
  run_grover(CNF, Oracle, Vars, NVar, NClauses, 1, Bound, A, Attempts).

% run_grover(+CNF, +Oracle, +Vars, +NVar, +NClauses, +Iters, +Bound, -A, -Attempts)
run_grover(CNF, Oracle, Vars, NVar, NClauses, Iters, Bound, A, Attempts) :-
  format("Running grover with ~d~n", [Iters]),
  ( Iters > Bound -> A = unknown, Attempts = []
  ; py_call(pymain:run_grover(Oracle, NVar, NClauses, Iters), R-PyAttemptMetrics),
    attempt_metrics_term(PyAttemptMetrics, Attempt),
    ( verify(CNF, Vars, R, VR), VR = [_|_] ->
        assignment(VR, Vars, Assignment),
        A = sat(Assignment),
        Attempts = [Attempt]
    ; NewIters is min(ceiling(Iters * 3 / 2), Bound),
      ( NewIters > Iters ->
          run_grover(CNF, Oracle, Vars, NVar, NClauses, NewIters, Bound, A, RestAttempts),
          Attempts = [Attempt|RestAttempts]
      ; A = unknown, Attempts = [Attempt]
      )
    )
  ).

% oracle_metrics_term(+PyDict, -Term) converts the metrics dict returned by
% pymain:oracle/1 (a Python dict, arriving as a SWI dict) into a plain term.
oracle_metrics_term(D, oracle_metrics(NVars, NClauses, NQubits, NAncillas, MCXCount, Depth, GateCounts, BuildTime)) :-
  get_dict(n_vars, D, NVars),
  get_dict(n_clauses, D, NClauses),
  get_dict(n_qubits, D, NQubits),
  get_dict(n_ancillas, D, NAncillas),
  get_dict(mcx_count, D, MCXCount),
  get_dict(depth, D, Depth),
  get_dict(gate_counts, D, GateCounts),
  get_dict(build_time, D, BuildTime).

% attempt_metrics_term(+PyDict, -Term) converts the metrics dict returned by
% pymain:run_grover/4 for a single BBHT attempt into a plain term.
attempt_metrics_term(D, attempt_metrics(IterationsUsed, MaxIterations, SimTime, Shots, Counts)) :-
  get_dict(iterations_used, D, IterationsUsed),
  get_dict(max_iterations, D, MaxIterations),
  get_dict(sim_time, D, SimTime),
  get_dict(shots, D, Shots),
  get_dict(counts, D, Counts).

% python_error_string(+Error, -Msg) converts a Prolog exception into a
% plain readable atom, e.g. 'CircuitError: duplicate bit arguments'.
%
% janus reports Python exceptions as error(python_error(ErrorType, Value), _),
% where Value is an opaque Python object reference -- NOT a string, and
% janus has no py_str/2 to stringify it directly. There IS a print_message/2
% rule registered for this shape (so print_message/2 renders it nicely,
% backtrace included), but for a clean one-line string we instead call
% Python's own str() on Value via py_call/2, and pair it with ErrorType
% ourselves. Any other kind of Prolog exception (e.g. a type_error from
% janus's own data conversion) falls back to message_to_string/2.
python_error_string(error(python_error(Type, Value), _Context), Msg) :-
  !,
  ( catch(py_call(str(Value), ValueStr), _, fail) -> true ; ValueStr = '<unavailable>' ),
  format(atom(Msg), "~w: ~w", [Type, ValueStr]).
python_error_string(Error, Msg) :-
  message_to_string(Error, Str),
  atom_string(Msg, Str).

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