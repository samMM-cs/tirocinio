:- use_module('main.pro').
:- use_module('quantum.pro').
:- use_module('sat_parse.pro').
:- use_module('cnf.pro').
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(random)).

:- dynamic instance/3.

instance(unit1, unit_clause, "A && (!A || B) && (!B || C)").
instance(unit2, unit_clause, "A && !B && (A || B || C)").

instance(pure1, pure_literal, "(A || B) && (A || C) && (B || C)").
instance(pure2, pure_literal, "(A || B || C) && (A || !B) && (A || !C)").
% pure3 demonstrates a *cascade*: C is pure and gets forced first, which then makes A and B pure (in the opposite polarity) in what's left.
instance(pure3, pure_literal, "(A || B || C) && (!A || !B)").

% taut1 fails without tautology elimination because the oracle needs to build a controlled gate with the same control and target qubit 
instance(taut1, tautology, "A || !A").
% same as before for taut2, but pure literal elimination solves as well
instance(taut2, tautology, "(A && B) -> A").

instance(sat_single1, sat_single, "A && B && !C").
instance(sat_single2, sat_single, "(A -> B) && A && (B -> C) && !D && (D -> A)").

% Neither A nor B is pure here (each appears both polarities), so this keeps both of its satisfying assignments (A=T,B=F and A=F,B=T) even under full preprocessing.
instance(sat_multi1, sat_multi, "(A || B) && (!A || !B)").
% A and B do get pure-literal-forced to true here, but C and D remain genuinely undetermined (C=D=T or C=D=F both satisfy), so two solutions survive.
instance(sat_multi2, sat_multi, "(A || B) && (C || !D) && (!C || D)").

instance(unsat1, unsat, "A && !A").
% Unlike unsat1, this is NOT resolved by tautology removal, unit propagation, or pure literal elimination alone or combined -- it needs branching/resolution to detect. It is included specifically to exercise the "budget exceeded is not proof of unsat" path: sol/4 will report `unknown` for this instance, not `unsat`, under every configuration.
instance(unsat2, unsat, "(A || B) && (!A || B) && (A || !B) && (!A || !B)").

instance(rand_gen(10), random, "((((V18 ^ V18) ^ (V1 ^ V11)) || V10) && (((V10 || V6) && !V13) || ((V9 ^ V7) || (V8 || V17))))").
instance(rand_gen(9), random, "((((V11 ^ V20) ^ !V19) && V1) && (!(V19 && V1) ^ V14))").
instance(rand_gen(8), random, "((!(!V8 || !V13) -> ((!V2 && (V5 -> V7)) ^ ((V2 -> V7) -> (V18 || V12)))) || V18)").
instance(rand_gen(7), random, "(((V12 ^ V2) ^ (V2 -> V5)) -> ((V13 -> V12) && (V8 || V1)))").
instance(rand_gen(6), random, "((((V2 ^ V3) ^ (V4 ^ V2)) || !(V4 ^ V3)) ^ !V1)").
instance(rand_gen(5), random, "(!(!V15 -> V16) || (((V16 && V8) || (V2 && V2)) && (!V10 && (V1 ^ V11))))").
instance(rand_gen(4), random, "(!((V7 || V8) && (V2 || V14)) ^ (!(V13 || V9) || (V9 || !V14)))").
instance(rand_gen(3), random, "((!(V5 ^ V7) || ((V2 || V6) || (V9 ^ V4))) && (((V1 || V4) -> (V10 ^ V14)) || (V4 && (V10 ^ V14))))").
instance(rand_gen(2), random, "(V8 ^ ((((V4 ^ V9) || (V3 && V7)) || V7) || ((!V4 || (V5 ^ V10)) || (!V9 -> (V3 -> V3)))))").
instance(rand_gen(1), random, "((V2 ^ (V6 || (V5 ^ V10))) -> (((V5 && V5) ^ V2) && (V2 && (V7 || V2))))").
instance(rand_gen(0), random, "(((V3 -> ((V4 && V6) -> (V4 ^ V1))) -> (V3 -> !(V3 && V4))) -> ((!(V1 && V6) -> ((V1 ^ V5) ^ !V1)) || !!(V5 -> V1)))").


% ---------------------------------------------------------------------
% Helper Predicates
% ---------------------------------------------------------------------


add_random_instances(N) :- 
  integer(N),
  N >= 0, !,
  generate_valid_instance(FormulaStr, _),
  assertz(instance(rand_gen(N), random, FormulaStr)),
  N1 is N - 1,
  add_random_instances(N1).
add_random_instances(_).

% generate_valid_instance(-FormulaStr, -NVars)
%
% Generates a random instance whose oracle qubit count (n_vars + n_clauses
% + 1 output qubit) is as close as possible to, but not exceeding, the
% 29-qubit budget -- rather than just accepting the first candidate that
% happens to fit under the limit.
generate_valid_instance(FormulaStr, NVars) :-
    generate_near_target(29, 200, FormulaStr, NVars).

% generate_near_target(+Target, +Attempts, -FormulaStr, -NVars)
% Draws up to Attempts random candidates (skipping ones that fail to
% parse/cnfify or time out) and keeps the one with the highest qubit
% count that still respects Target.
generate_near_target(Target, Attempts, FormulaStr, NVars) :-
    findall(Qubits-(Str-NV),
        ( between(1, Attempts, _),
          catch(random_instance(Target, Str, NV, Qubits), _, fail)
        ),
        Candidates),
    Candidates \= [],  % raise a clear error instead of silently failing if every attempt failed
    keysort(Candidates, Sorted),
    last(Sorted, _-(FormulaStr-NVars)).

% random_instance(+Target, -FormulaStr, -NVars, -TotalQubits)
random_instance(Target, FormulaStr, NVars, TotalQubits) :-
    MaxVars is min(20, Target - 1),        % leave room for >=1 clause+output qubit
    random_between(2, MaxVars, NVars),
    findall(VarAtom,
            ( between(1, NVars, I), atom_concat('V', I, VarAtom) ),
            VarList),
    random_between(2, 5, Depth),           % randomize depth too, not just var count
    gen_ast(Depth, VarList, AST),
    ast_to_str(AST, FormulaStr),
    % guard against distribute/2's exponential blowup on deep xor/implies nesting
    call_with_time_limit(2, catch(cnfify(AST, none, CNF), _, fail)),
    is_list(CNF),
    length(CNF, NClauses),
    TotalQubits is NVars + NClauses + 1,
    TotalQubits =< Target.

% AST Construction (unchanged apart from weighting -- see note below)
gen_ast(0, VarList, var(Var)) :- !,
    random_member(Var, VarList).
gen_ast(Depth, VarList, AST) :-
    D1 is Depth - 1,
    random_between(1, 6, Choice),
    ( Choice =:= 1 -> AST = var(Var), random_member(Var, VarList)
    ; Choice =:= 2 -> gen_ast(D1, VarList, Sub), AST = not(Sub)
    ; Choice =:= 3 -> gen_ast(D1, VarList, A), gen_ast(D1, VarList, B), AST = and(A, B)
    ; Choice =:= 4 -> gen_ast(D1, VarList, A), gen_ast(D1, VarList, B), AST = or(A, B)
    ; Choice =:= 5 -> gen_ast(D1, VarList, A), gen_ast(D1, VarList, B), AST = xor(A, B)
    ; Choice =:= 6 -> gen_ast(D1, VarList, A), gen_ast(D1, VarList, B), AST = implies(A, B)
    ).
% String Serialization
ast_to_str(var(X), Str) :- !, atom_string(X, Str).
ast_to_str(not(A), Str) :- !, ast_to_str(A, SA), string_concat("!", SA, Str).
ast_to_str(and(A, B), Str) :- !, fmt_binary(A, " && ", B, Str).
ast_to_str(or(A, B), Str) :- !, fmt_binary(A, " || ", B, Str).
ast_to_str(xor(A, B), Str) :- !, fmt_binary(A, " ^ ", B, Str).
ast_to_str(implies(A, B), Str) :- !, fmt_binary(A, " -> ", B, Str).

fmt_binary(A, Op, B, Str) :-
    ast_to_str(A, SA),
    ast_to_str(B, SB),
    string_concat("(", SA, S1),
    string_concat(S1, Op, S2),
    string_concat(S2, SB, S3),
    string_concat(S3, ")", Str).

% Batch pre-population helper predicate
seed_random_instances(Count) :-
    forall(
        between(1, Count, I),
        (
            atom_concat(gen_rand_, I, Id),
            generate_valid_instance(FormulaStr, _),
            assertz(instance(Id, random, FormulaStr))
        )
    ).


% ---------------------------------------------------------------------
% Optimization configurations: the power set of the three independently
% toggleable optimize/3 passes.
% ---------------------------------------------------------------------

optimize_config([]).
optimize_config([tautology]).
optimize_config([unit_propagation]).
optimize_config([pure_literal]).
optimize_config([tautology, unit_propagation]).
optimize_config([tautology, pure_literal]).
optimize_config([unit_propagation, pure_literal]).
optimize_config([tautology, unit_propagation, pure_literal]).

% config_str(+Config, -Str) gives a short display/CSV-safe label for a
% configuration: `none` and `full` for the two extremes (readability),
% otherwise the enabled optimizations joined with '+' (no commas, so it's
% safe to drop straight into a CSV field unquoted).
config_str([], none) :- !.
config_str([tautology, unit_propagation, pure_literal], full) :- !.
config_str(Config, Str) :-
  atomic_list_concat(Config, '+', Str).

% ---------------------------------------------------------------------
% Running a single instance under a single configuration
% ---------------------------------------------------------------------

% run_instance(+Id, +Config, -Result)
%
% Result = result(Id, Category, Config, A, Metrics, WallTime)
%   A       - unsat / tautology / sat(Assignment) / unknown / error(Msg),
%             where Msg is a plain readable atom (see quantum:python_error_string/2)
%   Metrics - metrics(none, []) or metrics(OracleMetrics, Attempts), see
%             quantum.pro
%   WallTime - end-to-end wall-clock seconds for this single run
run_instance(Id, Config, result(Id, Category, Config, A, Metrics, WallTime)) :-
  instance(Id, Category, Formula),
  get_time(T0),
  ( catch(sol(Formula, Config, A, Metrics), Error,
          ( python_error_string(Error, Msg),
            A = error(Msg),
            Metrics = metrics(none, [])
          ))
  -> true
  ;  A = failed, Metrics = metrics(none, [])
  ),
  get_time(T1),
  WallTime is T1 - T0.

% ---------------------------------------------------------------------
% Batch runners
% ---------------------------------------------------------------------

% for_each_result(:Goal) runs every instance x configuration pair (in the
% order given by instance/3 x optimize_config/1) and, immediately after
% EACH single run completes, calls call(Goal, Index, Total, Result) --
% before moving on to the next pair. This is the shared primitive behind
% run_all/0 and results_to_csv/1: it lets a caller act on (print, write
% to disk, ...) each result the moment it's ready, rather than only after
% the whole batch finishes.
for_each_result(Goal) :-
  findall(Id-Config,
          (instance(Id, _, _), optimize_config(Config)),
          Pairs),
  length(Pairs, Total),
  format("Running ~d instance x configuration combinations...~n", [Total]),
  for_each_result_(Pairs, 1, Total, Goal).

for_each_result_([], _, _, _).
for_each_result_([Id-Config|T], I, Total, Goal) :-
  run_instance(Id, Config, R),
  call(Goal, I, Total, R),
  I1 is I + 1,
  for_each_result_(T, I1, Total, Goal).

% run_all/0 runs every instance under every configuration (15 instances x
% 8 configs = 120 runs), printing a one-line summary as each completes.
% Nothing is accumulated in memory -- see run_all/1 if you want the full
% list of results back for further in-session analysis, or
% results_to_csv/1 if you want each result persisted to disk as it lands.
run_all :-
  for_each_result(print_progress),
  format("~nDone.~n").

print_progress(I, Total, result(Id, _Category, Config, A, _Metrics, WallTime)) :-
  config_str(Config, Str),
  instance(Id, _, Expr),
  format("[~d/~d] ~w  ~w  ~w ... ~w  (~3f s)~n", [I, Total, Id, Str, Expr, A, WallTime]).

% run_all(-Results) collects every Result into a list instead of writing
% or printing incrementally -- for interactive use when you want
% everything in memory at once (e.g. to inspect/filter in the toplevel).
% For anything long-running or unattended, prefer results_to_csv/1, which
% persists each row to disk as soon as it's computed instead of holding
% the whole batch in memory until the end.
run_all(Results) :-
  findall(Id-Config,
          (instance(Id, _, _), optimize_config(Config)),
          Pairs),
  maplist(run_pair, Pairs, Results).

run_pair(Id-Config, R) :-
  run_instance(Id, Config, R).

% run_category(+Category, -Results) restricts to one category, all 8
% configs -- useful for focusing on e.g. just the unsat instances.
run_category(Category, Results) :-
  findall(Id, instance(Id, Category, _), Ids),
  Ids \= [],
  findall(R,
          ( member(Id, Ids),
            optimize_config(Config),
            run_instance(Id, Config, R)
          ),
          Results).

% ---------------------------------------------------------------------
% CSV export
% ---------------------------------------------------------------------

% results_to_csv(+Path) runs everything and writes a flat CSV, one row
% per instance x configuration, suitable for the evaluation tables/plots.
% Oracle/attempt fields are left blank ('') for runs that never reached
% the quantum module (unsat/tautology/error/failed).
%
% Each row is written AND flushed to the underlying file as soon as that
% single instance x configuration run completes -- not batched up and
% written only once the full run finishes. That way, if a later run in
% the batch crashes, hangs, or the process gets killed, every row
% computed so far is already durably on disk instead of lost.
results_to_csv(Path) :-
  setup_call_cleanup(
    open(Path, write, Stream),
    ( write_csv_header(Stream),
      flush_output(Stream),
      for_each_result(write_progress_and_row(Stream))
    ),
    close(Stream)
  ),
  format("~nWrote results to ~w~n", [Path]).

write_progress_and_row(Stream, I, Total, R) :-
  print_progress(I, Total, R),
  write_csv_row(Stream, R),
  flush_output(Stream).

write_csv_header(Stream) :-
  format(Stream,
    "id,category,formula,config,outcome,n_valid_assignments,n_vars,n_clauses,n_qubits,n_ancillas,mcx_count,depth,build_time,n_attempts,total_sim_time,total_iterations,wall_time~n",
    []).

write_csv_row(Stream, result(Id, Category, Config, A, Metrics, WallTime)) :-
  % Retrieve original formula string; default to empty string if missing
  ( instance(Id, _, Formula) -> true ; Formula = "" ),
  config_str(Config, ConfigStr),
  outcome_atom(A, Outcome),
  n_valid_assignments(A, NValid),
  ( Metrics = metrics(oracle_metrics(NVars, NClauses, NQubits, NAncillas,
                                      MCXCount, Depth, _GateCounts, BuildTime),
                       Attempts)
  -> length(Attempts, NAttempts),
     total_sim_time(Attempts, TotalSimTime),
     total_iterations(Attempts, TotalIters)
  ;  NVars = '', NClauses = '', NQubits = '', NAncillas = '', MCXCount = '',
     Depth = '', BuildTime = '', NAttempts = 0, TotalSimTime = '', TotalIters = ''
  ),
  % ~q formats Formula enclosed in quotes
  format(Stream, "~w,~w,~q,~w,~w,~w,~w,~w,~w,~w,~w,~w,~w,~w,~w,~w,~3f~n",
    [Id, Category, Formula, ConfigStr, Outcome, NValid, NVars, NClauses, NQubits, NAncillas,
     MCXCount, Depth, BuildTime, NAttempts, TotalSimTime, TotalIters, WallTime]).
outcome_atom(unsat, unsat) :- !.
outcome_atom(tautology, tautology) :- !.
outcome_atom(unknown, unknown) :- !.
outcome_atom(sat(_), sat) :- !.
outcome_atom(error(_), error) :- !.
outcome_atom(failed, failed) :- !.
outcome_atom(A, A).

n_valid_assignments(sat(Assignment), N) :- !, length(Assignment, N).
n_valid_assignments(_, 0).


total_sim_time(Attempts, Total) :-
  findall(T, member(attempt_metrics(_, _, T, _, _), Attempts), Ts),
  sum_list(Ts, Total).

total_iterations(Attempts, Total) :-
  findall(It, member(attempt_metrics(It, _, _, _, _), Attempts), Its),
  sum_list(Its, Total).