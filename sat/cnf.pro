:- module(cnf, [cnfify/2]).

% cnfify(AST, T) reduces AST to CNF and simplifies its representation
cnfify(AST, L) :-
  eliminate(AST, E), % keep basic operators
  distribute(E, CNF), % bring to CNF
  % write(CNF),
  process(CNF, UL),
  optimize(UL, P),
  ( is_list(P) -> sort(P, L)
  ; L = P).

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
% optimize(UL, L) applies Unit Propagation to simplify the CNF clauses
optimize(UL, L) :-
  remove_tautologies(UL, RT),
  optimize_units(RT, [], L).

% optimize_units(RemainingClauses, AccumulatedUnits, FinalClauses)
optimize_units(RT, Units, L) :-
  ( member([]-[], RT) -> L = unsat
  ; RT = [] ->
      ( Units = [] -> L = sat
      ; append(Units, RT, L)
      )
  % 1. Propagate True Units
  ; select([]-[A], RT, Rest) ->
      propagate_true(A, Rest, NewRT),
      optimize_units(NewRT, [[]-[A]|Units], L)
  % 2. Propagate False Units
  ; select([A]-[], RT, Rest) ->
      propagate_false(A, Rest, NewRT),
      optimize_units(NewRT, [[A]-[]|Units], L)
  % 3. Pure Literal Elimination
  ; gather_literals(RT, AllN, AllS),
    ord_subtract(AllN, AllS, PureN),
    ord_subtract(AllS, AllN, PureS),
    ( PureN \= [] ; PureS \= [] ) ->
        eliminate_pure(PureN, PureS, RT, NewRT),
        make_units(PureN, PureS, PureUnits),
        append(PureUnits, Units, NewUnits),
        optimize_units(NewRT, NewUnits, L)
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