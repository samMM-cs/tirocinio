:- module(cnf, [cnfify/2, cnfify/3]).


% cnfify(AST, L) reduces AST to CNF and simplifies its representation,
% applying the full optimize/2 pass (tautology removal, unit propagation,
% pure literal elimination). Equivalent to cnfify(AST, full, L).
cnfify(AST, L) :-
  cnfify(AST, full, L).

% cnfify(AST, Optimize, L) as above, but Optimize controls which parts of the optimize/2 pass run. It may be:
%   full          - apply all three optimizations (same as cnfify/2)
%   none          - apply none of them; L is the raw simplified clause list
%   a list, any subset of [tautology, unit_propagation, pure_literal]
%                 - apply exactly those optimizations, independently
% e.g. cnfify(AST, [pure_literal], L) runs pure literal elimination only, skipping tautology removal and unit propagation.
% Used to build the oracle from a partially- or un-preprocessed CNF, to measure each optimization's individual effect on circuit resource use.
% Note: L is only ever bound to sat/unsat when unit_propagation is enabled (that's the only step that can reduce the clause list to empty or to a single empty clause) -- with unit_propagation absent from the option set, L is always a genuine (possibly still-reducible) clause list.
cnfify(AST, Optimize, L) :-
  optimize_opts(Optimize, Opts),
  eliminate(AST, E), % keep basic operators
  distribute(E, CNF), % bring to CNF
  % write(CNF),
  process(CNF, UL),
  optimize(UL, Opts, P),
  ( is_list(P) -> sort(P, L)
  ; L = P).

optimize_opts(full, [tautology, unit_propagation, pure_literal]) :- !.
optimize_opts(none, []) :- !.
optimize_opts(Opts, Opts) :-
  is_list(Opts), !,
  ( forall(member(O, Opts), valid_optimize_opt(O)) -> true
  ; domain_error(optimize_opts, Opts)
  ).
optimize_opts(Optimize, _) :-
  domain_error(optimize_opts, Optimize).

valid_optimize_opt(tautology).
valid_optimize_opt(unit_propagation).
valid_optimize_opt(pure_literal).

% eliminate(AST, E) iff E is the boolean expression AST written only with and, or, literals and negated literals
% base case: literals
eliminate(var(A), var(A)).
eliminate(not(var(A)), not(var(A))).
% A => B becomes !A||B
eliminate(implies(A, B), E) :-
  eliminate(or(not(A), B), E).
% !(A => B) becomes A && !B
eliminate(not(implies(A, B)), E) :-
  eliminate(and(A, not(B)), E).
% !(A <=> B) becomes A xor B
eliminate(not(equiv(A, B)), E) :-
  eliminate(xor(A, B), E).
% !(A xor B) becomes A <=> B
eliminate(not(xor(A, B)), E) :-
  eliminate(equiv(A, B), E).
% A <=> B becomes A=>B&&B=>A
eliminate(equiv(A, B), E) :- 
  eliminate(and(implies(A, B), implies(B, A)), E).
% A xor B becomes (A||B)&&!(A&&B)
eliminate(xor(A, B), E) :-
  eliminate(and(or(A, B), not(and(A, B))), E).
% double negation elimination
eliminate(not(not(A)), E) :-
  eliminate(A, E).
% de morgan's laws
eliminate(not(and(A, B)), E) :-
  eliminate(or(not(A), not(B)), E).
eliminate(not(or(A, B)), E) :-
  eliminate(and(not(A), not(B)), E).
% after eliminating other operators, recurse on deeper levels
eliminate(and(A, B), and(EA, EB)) :-
  eliminate(A, EA),
  eliminate(B, EB).
eliminate(or(A, B), or(EA, EB)) :-
  eliminate(A, EA),
  eliminate(B, EB).

% distribute(EXPR, CNF) iff CNF is the cnf form of EXPR
% base case: literals and negated literals
distribute(var(A), var(A)).
distribute(not(var(A)), not(var(A))).
% and should be on top level, so simply recurse one level lower
distribute(and(A, B), and(EA, EB)) :-
  distribute(A, EA),
  distribute(B, EB).
% or might have to be pushed lower
distribute(or(A, B), CNF) :-
  distribute(A, EA),
  distribute(B, EB),
  distribute_or(or(EA, EB), CNF).
% push or inside of and
distribute_or(or(and(A, B), C), and(E1, E2)) :-
  !,
  distribute_or(or(A, C), E1),
  distribute_or(or(B, C), E2).
distribute_or(or(A, and(B, C)), and(E1, E2)) :-
  !,
  distribute_or(or(A, B), E1),
  distribute_or(or(A, C), E2).
distribute_or(or(A, B), or(A, B)) :- !.

has_and(and(_, _)).
has_and(or(A, B)) :-
  has_and(A); has_and(B).


% process(CNF, L) converts a cnf AST to a simpler representation
process(CNF, L) :- phrase(process_and(CNF), P), simplify(P, L).

% if and found, just concat the two
process_and(and(A, B)) --> process_and(A), process_and(B).
process_and(or(A, B)) --> {phrase(process_or(or(A, B)), L)}, [L].
process_and(var(A)) --> [[var(A)]].
process_and(not(var(A))) --> [[not(var(A))]].

process_or(or(A, B)) --> process_or(A), process_or(B).
process_or(var(A)) --> [var(A)].
process_or(not(var(A))) --> [not(var(A))].

% simplify(CL, L) simplifies the clauses given by CL in a list of pairs of lists format where each pair is a disjunction of the negated literals in its first part and the straight literals in its second part
simplify([], []).
simplify([C|T], [N-S|R]) :-
  sort(C, CS),
  partition(is_negated, CS, N_, S_),
  keep_names(N_, N),
  keep_names(S_, S),
  simplify(T, R).

is_negated(not(_)).

keep_names([], []).
keep_names([var(A)|T], [A|R]) :- keep_names(T, R).
keep_names([not(var(A))|T], [A|R]) :- keep_names(T, R).
% optimize(UL, Opts, L) applies the optimizations named in Opts (a subset of [tautology, unit_propagation, pure_literal]) to simplify the CNF clauses.
optimize(UL, Opts, L) :-
  ( memberchk(tautology, Opts) -> remove_tautologies(UL, RT) ; RT = UL ),
  optimize_units(RT, [], Opts, L).

% optimize_units(RemainingClauses, AccumulatedUnits, Opts, FinalClauses)
optimize_units(RT, Units, Opts, L) :-
  ( member([]-[], RT) -> L = unsat
  ; RT = [] ->
      ( Units = [] -> L = sat
      ; append(Units, RT, L)
      )
  % 1. Propagate True Units
  ; memberchk(unit_propagation, Opts), select([]-[A], RT, Rest) ->
      propagate_true(A, Rest, NewRT),
      optimize_units(NewRT, [[]-[A]|Units], Opts, L)
  % 2. Propagate False Units
  ; memberchk(unit_propagation, Opts), select([A]-[], RT, Rest) ->
      propagate_false(A, Rest, NewRT),
      optimize_units(NewRT, [[A]-[]|Units], Opts, L)
  % 3. Pure Literal Elimination
  ; memberchk(pure_literal, Opts),
    gather_literals(RT, AllN, AllS),
    ord_subtract(AllN, AllS, PureN),
    ord_subtract(AllS, AllN, PureS),
    ( PureN \= [] ; PureS \= [] ) ->
        eliminate_pure(PureN, PureS, RT, NewRT),
        make_units(PureN, PureS, PureUnits),
        append(PureUnits, Units, NewUnits),
        optimize_units(NewRT, NewUnits, Opts, L)
  % 4. Done optimizing, return remaining
  ; append(Units, RT, L)
  ).

% propagate_true(A, Clauses, CleanedClauses)
propagate_true(_, [], []).
propagate_true(A, [N-S|T], R) :-
  ( member(A, S) ->
      propagate_true(A, T, R)
  ; member(A, N) ->
      select(A, N, NewN),
      R = [NewN-S|NewR],
      propagate_true(A, T, NewR)
  ; R = [N-S|NewR],
      propagate_true(A, T, NewR)
  ).

% propagate_false(A, Clauses, CleanedClauses)
propagate_false(_, [], []).
propagate_false(A, [N-S|T], R) :-
  ( member(A, N) ->
      propagate_false(A, T, R)
  ; member(A, S) ->
      select(A, S, NewS),
      R = [N-NewS|NewR],
      propagate_false(A, T, NewR)
  ; R = [N-S|NewR],
      propagate_false(A, T, NewR)
  ).

remove_tautologies([], []).
remove_tautologies([N-S|T], R) :-
  ( ord_disjoint(N, S) -> R = [N-S|O]
                        ; R = O),
  remove_tautologies(T, O).

% Gather all literals as ordered sets
gather_literals([], [], []).
gather_literals([N-S|T], AllN, AllS) :-
    gather_literals(T, RestN, RestS),
    ord_union(N, RestN, AllN),
    ord_union(S, RestS, AllS).

% Eliminate clauses that contain pure literals
eliminate_pure(_, _, [], []).
eliminate_pure(PureN, PureS, [N-S|T], R) :-
    ( ord_intersect(PureN, N) -> eliminate_pure(PureN, PureS, T, R)
    ; ord_intersect(PureS, S) -> eliminate_pure(PureN, PureS, T, R)
    ; R = [N-S|NewR], eliminate_pure(PureN, PureS, T, NewR)
    ).

% Convert pure literals to unit clauses for the assignment tracker
make_units([], [], []).
make_units([N|Tn], S, [[N]-[]|Rest]) :- make_units(Tn, S, Rest).
make_units([], [S|Ts], [[]-[S]|Rest]) :- make_units([], Ts, Rest).