:- use_module(library(clpfd)).
:- set_prolog_flag(answer_write_options, [quoted(true), portray(true), max_depth(0)]).

% ========================== LISTS ==========================

my_last(A, [A]).
my_last(X, [_H|T]) :- my_last(X, T).

my_second_last(A, [A, _J]).
my_second_last(X, [_H|T]) :- my_second_last(X, T).

element_at(H, [H|_T], 1).
element_at(X, [_H|T], N) :-
  N #> 1,
  K #= N - 1,
  element_at(X, T, K).

my_length([], 0).
my_length([_H|T], N) :-
  N #= N1 + 1,
  my_length(T, N1).

rev(L, R) :- rev(L, [], R).
rev([], R, R).
rev([H|T], A, R) :- rev(T, [H|A], R).

is_palindrome(L) :- rev(L, L).

my_flatten(L, F) :- my_flatten(L, F, []).
my_flatten([], F, F).
my_flatten([H|T], A, F) :-
  (
    is_list(H) 
  -> my_flatten(H, A, N), 
     my_flatten(T, N, F)
  ;  A = [H|AT], 
     my_flatten(T, AT, F)
  ).

compress([], []).
compress([X], [X]).
compress([H, H|T], L) :- compress([H|T], L).
compress([H, Y|T], [H|L]) :-
  H \= Y,
  compress([Y|T], L).

pack([], []).
pack([H|T], P) :- pack(T, [H], P).
pack([], A, [A]).
pack([H|T], [H|A], P) :-
  !,
  pack(T, [H, H|A], P).
pack([H|T], A, [A|P]) :- pack(T, [H], P).   

encode(L, E) :-
  pack(L, P),
  encode_packed(P, E).
encode_packed([], []).
encode_packed([[E|R]|T], [[N, E]|X]) :-
  my_length([E|R], N),
  encode_packed(T, X).


encode_modified(L, E) :-
  pack(L, P),
  encode_packed_modified(P, E).
encode_packed_modified([], []).
encode_packed_modified([[E]|T], [E|X]) :-
  !,
  encode_packed_modified(T, X).
encode_packed_modified([[E|R]|T], [[N, E]|X]) :-
  my_length([E|R], N),
  encode_packed_modified(T, X).

decode([], []).
decode([E|T], [E|D]) :-
  not(is_list(E)),
  !,
  decode(T, D).
decode([[0, _E]|T], D) :-
  !,
  decode(T, D).
decode([[N, E]|T], [E|R]) :-
  N #> 0,
  K #= N - 1,
  decode([[K, E]|T], R).

encode_direct([], []).
encode_direct([H|T], E) :- encode_direct(T, H, 1, E).
encode_direct([], E, N, [[N, E]]).
encode_direct([H|T], H, N, E) :-
  !,
  K #= N + 1,
  encode_direct(T, H, K, E).
encode_direct([H|T], X, N, [[N, X]|E]) :- encode_direct(T, H, 1, E).

encode_direct_modified(L, E) :-
  encode_direct(L, P),
  process(P, E).
process([], []).
process([[1, X]|T], [X|E]) :- !, process(T, E).
process([[N, X]|T], [[N, X]|E]) :- process(T, E).

dupli(L, D) :- dupli(L, 2, D).
dupli([], _N, []).
dupli([H|T], N, D) :-
  prepend_n(H, N, L, D),
  dupli(T, N, L).

prepend_n(_H, 0, L, L).
prepend_n(H, N, L, [H|P]) :-
  N #> 0,
  K #= N - 1,
  prepend_n(H, K, L, P).

drop_every(L, N, D) :-
  N #> 0,
  drop_every(L, N, N, [], D).
drop_every([], _, _, A, D) :- reverse(A, D).
drop_every([_H|T], N, 1, A, D) :- !, drop_every(T, N, N, A, D).
drop_every([H|T], N, K, A, D) :-
  K #> 1,
  M #= K - 1,
  drop_every(T, N, M, [H|A], D).

split(L, 0, [], L).
split([H|T], N, [H|L1], L2) :-
  N #> 0,
  K #= N - 1,
  split(T, K, L1, L2).

slice([H|_T], 1, 1, [H]).
slice([H|T], 1, N, [H|L]) :-
  N #> 1,
  K #= N - 1,
  slice(T, 1, K, L).
slice([_H|T], I, N, L) :-
  I #> 1,
  N #>= I,
  I1 #= I - 1,
  N1 #= N - 1,
  slice(T, I1, N1, L).

rotate(L, 0, L).
rotate(L, N, R) :-
  my_length(L, M),
  N #> 0,
  K #= N mod M,
  split(L, K, A, B),
  append(B, A, R).
rotate(L, N, R) :-
  my_length(L, M),
  N #< 0,
  K #= M + N,
  rotate(L, K, R).

remove_at(H, [H|T], 1, T).
remove_at(X, [H|T], N, [H|R]) :-
  N #> 1,
  K #= N - 1,
  remove_at(X, T, K, R).

insert_at(H, T, 1, [H|T]).
insert_at(X, [H|T], N, [H|L]) :-
  K #= N - 1,
  insert_at(X, T, K, L).

range(N, N, [N]).
range(A, B, [A|L]) :-
  A #< B,
  A1 #= A + 1,
  range(A1, B, L).

rnd_select(_L, 0, []).
rnd_select(L, N, [X|S]) :-
  N #> 0,
  my_length([_|L], M),
  random(1, M, I),
  K #= N - 1,
  remove_at(X, L, I, R),
  rnd_select(R, K, S).
  
lotto(N, M, L) :-
  N #=< M,
  range(1, M, R),
  rnd_select(R, N, L).

rnd_perm(L, P) :-
  my_length(L, N),
  rnd_select(L, N, P).

combination(0, _L, []).
combination(N, [H|T], [H|C]) :-
  N #> 0,
  K #= N - 1,
  combination(K, T, C).
combination(N, [_H|T], C) :-
  N #> 0,
  combination(N, T, C).

group3(G, G1, G2, G3) :-
  selectN(2, G, G1),
  subtract(G, G1, R1),
  selectN(3, R1, G2),
  subtract(R1, G2, R2),
  selectN(4, R2, G3),
  subtract(R2, G3, []).
  
% selectN(N, L, S) :- select N elements of L into S, gives all selections by backtracking
selectN(0, _L, []).
selectN(N, L, [X|S]) :-
  N > 0,
  el(X, L, R),
  % get an element of L
  N1 #= N - 1,
  selectN(N1, R, S).% select N - 1 elements of R
  % el(X, L, R) :- true iff X is an element of L and R is the remainder of the list
  el(X, [X|L], L).

el(X, [_|L], R) :- el(X, L, R).

% group(L, C, G) :- group the elements of L into groups in G, lengths of G are given in C
group([], [], []).
group(L, [C|Cs], [G|Gs]) :-
  selectN(C, L, G),
  subtract(L, G, M),
  group(M, Cs, Gs).

% lsort(I, O) :- sorts I into O according to the lengths of its elements
lsort(I, S) :-
  map_list_to_pairs(length, I, IL),
  keysort(IL, P),
  pairs_values(P, S).

% lfsort(I, O) :- sorts I into O according to the frequency of the lengths of its elements
lfsort(I, S) :-
  map_list_to_pairs(length, I, IL),
  keysort(IL, P),
  pack_pairs(P, PP),
  pairs_values(PP, V),
  lsort(V, VS),
  append(VS, S).

% pack_pairs(LP, P) :- packs the list of pairs LP into P by their keys
pack_pairs([], []).
pack_pairs([K-V|T], [K-[V|A]|R]) :-
  take_same(K, T, S, A),
  pack_pairs(S, R).

% take_same(K, P, R, V): gather all values of P with key K into V, put rest in R
take_same(K, [K-V|T], R, [V|A]) :- !, take_same(K, T, R, A).
take_same(_K, L, L, []).

% ========================== ARITHMETIC ==========================

is_prime(2).
is_prime(3).
is_prime(N) :-
  N #> 3,
  N mod 2 #\= 0,
  not(has_odd_factor(N, 3)).

has_odd_factor(N, F) :- N mod F #= 0.
has_odd_factor(N, F) :-
  F*F #< N,
  L #= F + 2,
  has_odd_factor(N, L).

gcd(A, 0, A) :- A > 0.
gcd(A, B, D) :-
  A1 #= A mod B,
  gcd(B, A1, D).

:- arithmetic_function(gcd/2).

coprime(A, B) :- gcd(A, B, 1).

% totient_phi(N, P) is true iff P is the number of integers 1 <= i < N coprime to N
totient_phi(1, 1).
totient_phi(N, P) :-
  N #>= 2,
  totient_phi(N, 1, 0, P).
totient_phi(N, N, P, P).
totient_phi(N, K, A, P) :-
  K #< N,
  coprime(N, K),
  K1 #= K + 1,
  A1 #= A + 1,
  totient_phi(N, K1, A1, P).
totient_phi(N, K, A, P) :-
  not(coprime(N, K)),
  K1 #= K + 1,
  totient_phi(N, K1, A, P).

prime_factors(0, []).
prime_factors(1, []).
prime_factors(N, [2|F]) :-
  N #> 1,
  N #= 2*K,
  prime_factors(K, F).
prime_factors(N, F) :-
  N #> 1,
  N #= 2*_K + 1,
  prime_factors(N, F, 3).
prime_factors(1, [], _F).
prime_factors(N, [P|F], P) :-
  N #= P*Q,
  Q #> 0,
  prime_factors(Q, F, P).
prime_factors(N, F, P) :-
  N #> 1,
  P1 #= P + 2,
  N mod P #\= 0,
  prime_factors(N, F, P1).

prime_factors_mult(N, F) :-
  prime_factors(N, PF),
  encode(PF, EF),
  swap(EF, F).

swap([], []).
swap([[A, B]|T], [[B, A]|S]) :- swap(T, S).

euler_phi(N, P) :-
  prime_factors_mult(N, F),
  euler_phi_calc(F, P).

euler_phi_calc([], 1).
euler_phi_calc([[P, M]|T], F) :-
  F #= F1*(P - 1)*P^(M - 1),
  euler_phi_calc(T, F1).

% no primes in an empty interval
prime_range(A, B, []) :- A #> B.
% skip 0 and 1, start with 2
prime_range(A, B, T) :-
  A #< 2,
  prime_range(2, B, T).
% if starts with 2, start with 2 and iterate on odd nums
prime_range(2, B, [2|T]) :-
  B #>= 2,
  prime_range(3, B, T).
% if A is even, skip it and iterate 
prime_range(A, B, T) :-
  A #> 2,
  A mod 2 #= 0,
  A1 #= A + 1,
  prime_range(A1, B, T).
% add an odd prime number and skip the even after it 
prime_range(A, B, [A|T]) :-
  A mod 2 #= 1,
  A #> 2,
  A #=< B,
  is_prime(A),
  A1 #= A + 2,
  prime_range(A1, B, T).
% iterate only on odd numbers
prime_range(A, B, T) :-
  A mod 2 #= 1,
  A #> 2,
  A #=< B,
  not(is_prime(A)),
  A1 #= A + 2,
  prime_range(A1, B, T).

goldbach(N, []) :- N mod 2 #= 1.
goldbach(N, []) :- N #=< 2.
goldbach(N, P) :-
  N #> 2,
  N mod 2 #= 0,
  prime_range(2, N, PL),
  findall([P1, P2], (
    member(P1, PL),
    P1 #=< P2,
    N #= P1 + P2,
    member(P2, PL)
  ), P).

goldbach_min(N, []) :- N mod 2 #= 1.
goldbach_min(N, []) :- N #=< 2.
goldbach_min(N, P) :-
  N #> 2,
  N mod 2 #= 0,
  M #= N // 2,
  prime_range(2, M, PL),
  goldbach_min(N, PL, P).
goldbach_min(N, [P|_T], [P, K]) :-
  K #= N - P,
  is_prime(K), !.
goldbach_min(N, [_P|T], L) :- goldbach_min(N, T, L).

goldbach_list(L, U, T) :-
    S #= max(4, L + (L mod 2)),
    iterate_goldbach(S, U, T).
iterate_goldbach(L, U, _) :- L #> U, !.
iterate_goldbach(L, U, T) :-
    goldbach_min(L, [P1, P2]),
    (P1 #>= T -> format('~d = ~d + ~d~n', [L, P1, P2]) ; true),
    L1 #= L + 2,
    iterate_goldbach(L1, U, T).

% ========================== LOGIC ==========================

and(A, B) :- A, B.
or(A, B) :- A; B.
nand(A, B) :- not(and(A, B)).
nor(A, B) :- not(or(A, B)).
xor(A, B) :- and(or(A, B), not(and(A, B))).
impl(A, B) :- or(not(A), B).
equ(A, B) :- not(xor(A, B)).

% bool(X) instantiate X to be true or false
bool(false).
bool(true).

table(A, B, E) :-
  bool(A),
  bool(B),
  line(A, B, E),
  fail.

line(A, B, E) :- 
  write(A), format('\t|'), write(B), format('\t|'), (E -> write(true) ; write(false)), nl.

:- op(900, fy,  not).
:- op(910, yfx, and).
:- op(910, yfx, nand).
:- op(920, yfx, or).
:- op(920, yfx, nor).
:- op(930, yfx, impl).
:- op(930, yfx, equ).
:- op(930, yfx, xor).

table_list(V, E) :-
  maplist(bool, V),
  line_list(V, E),
  fail.

line_list([], E) :- (E -> write(true) ; write(false)), nl.
line_list([V|T], E) :- 
  write(V), format('\t|'), 
  line_list(T, E). 

gray_code(1, ['0', '1']).
gray_code(N, C) :-
  N #> 1,
  K #= N - 1,
  gray_code(K, PC),
  rev(PC, PCR),
  prepend('0', PC, C0),
  prepend('1', PCR, C1),
  append(C0, C1, C).

prepend(_C, [], []).
prepend(C, [S|TS], [CS|T]) :- 
  string_concat(C, S, CS), 
  prepend(C, TS, T).

% huffman(F, C) :- C is the Huffman code for the frequencies in F
huffman([], []).
huffman([fr(L, _F)], L) :- is_list(L), !. % if reaching an only list, end
% if reaching a single symbol, assign it 0 or 1
huffman([fr(S, _F)], [hc(S, '0')]).
huffman([fr(S, _F)], [hc(S, '1')]).
huffman(F, C) :-
  % select two minimal frequency pairs
  select_min(F, A, F1),
  select_min(F1, B, F2),
  % pair them
  combine(A, B, P),
  % calculate huffman encoding of F2 with pairs
  huffman([P|F2], C).

select_min(F, E, R) :-
  min_weight(F, W),
  select_by_weight(W, F, E, R).

min_weight([fr(_S, W)], W).
min_weight([fr(_S, W)|T], MW) :-
  MW #= min(W, MW1),
  min_weight(T, MW1).

select_by_weight(W, [fr(S, W)|T], fr(S, W), T).
select_by_weight(W, [fr(S, F)|T], E, [fr(S, F)|R]) :-
  F #\= W,
  select_by_weight(W, T, E, R).

combine(A, B, C) :- combine_(A, B, C).
combine(A, B, C) :- combine_(B, A, C).

combine_(fr(SA, WA), fr(SB, WB), fr(SC, WC)) :-
  WC #= WA + WB,
  prepend_huffman('0', SA, CA),
  prepend_huffman('1', SB, CB),
  append(CA, CB, SC).

% if S is a symbol, just add it
prepend_huffman(P, S, [hc(S, P)]) :- not(is_list(S)).
prepend_huffman(_P, [], []). % base case, stop
prepend_huffman(P, [hc(S, C)|T], [hc(S, PC)|CT]) :-
  string_concat(P, C, PC),
  prepend_huffman(P, T, CT).
% ========================== TREES ==========================


tree(1,t(a,t(b,t(d,nil,nil),t(e,nil,nil)),t(c,nil,t(f,t(g,nil,nil),nil)))).
tree(2,t(a,nil,nil)).
tree(3,nil).

is_tree(nil).
is_tree(t(_V, L, R)) :- is_tree(L), is_tree(R).

cbal_tree(0, nil).
cbal_tree(1, t(x,nil,nil)).
cbal_tree(N1, t(x, L, R)) :-
  N #= N1 - 1,
  N #> 0,
  N #= 2 * K,
  cbal_tree(K, L),
  cbal_tree(K, R).
cbal_tree(N1, t(x, L, R)) :-
  N #= N1 - 1,
  N #> 0,
  N #= 2 * K + 1,
  K1 #= K + 1,
  cbal_tree(K1, L),
  cbal_tree(K, R).
cbal_tree(N1, t(x, L, R)) :-
  N #= N1 - 1,
  N #> 0,
  N #= 2 * K + 1,
  K1 #= K + 1,
  cbal_tree(K, L),
  cbal_tree(K1, R).

symmetric(nil).
symmetric(t(_N, L, R)) :- mirror(L, R).

mirror(nil, nil).
mirror(t(_N1, L1, R1), t(_N2, L2, R2)) :-
  mirror(L1, R2),
  mirror(R1, L2).

node_count(nil, 0).
node_count(t(_N, L, R), N) :-
  N #> 0,
  N #= NL + NR + 1,
  NL #>= 0,
  NR #>= 0,
  node_count(L, NL),
  node_count(R, NR).

construct_bst(L, T) :- construct_bst(L, T, nil).

construct_bst([], T, T).
construct_bst([E|R], T, A) :-
  add(E, A, A2),
  construct_bst(R, T, A2).

add(E, nil, t(E, nil, nil)).
add(E, t(X, L, R), t(X, L1, R)) :-
  E @=< X,
  add(E, L, L1).
add(E, t(X, L, R), t(X, L, R1)) :-
  E @> X,
  add(E, R, R1).

test_symmetric(L) :-
  construct_bst(L, T),
  symmetric(T).

sym_cbal_trees(N, TS) :- setof(T, sym_cbal_tree(N, T), TS), !.
sym_cbal_trees(_N, []).

sym_cbal_tree(N, T) :- cbal_tree(N, T), symmetric(T).

sym_cbal_trees_count(N, C) :- sym_cbal_trees(N, T), length(T, C).

hbal_tree(0, nil).
hbal_tree(H, t(x, L, R)) :-
  H #> 0,
  H1 #= H - 1,
  hbal_tree(H1, L),
  hbal_tree(H1, R).
hbal_tree(H, t(x, L, R)) :-
  H #> 1,
  H1 #= H - 1,
  H2 #= H - 2,
  hbal_tree(H1, L),
  hbal_tree(H2, R).
hbal_tree(H, t(x, L, R)) :-
  H #> 1,
  H1 #= H - 1,
  H2 #= H - 2,
  hbal_tree(H1, R),
  hbal_tree(H2, L).

min_nodes(0, 0).
min_nodes(1, 1).
min_nodes(H, N) :-
  H #> 1,
  H1 #= H - 1,
  H2 #= H - 2,
  N #= N1 + N2 + 1,
  min_nodes(H1, N1),
  min_nodes(H2, N2).

max_height(N, H) :- max_height(N, H, 0).
max_height(N, H, C) :-
  min_nodes(C, M),
  M #=< N,
  C1 #= C + 1,
  max_height(N, H, C1).
max_height(N, H, C) :-
  min_nodes(C, M),
  M #> N,
  H #= C - 1.

hbal_tree_nodes(N, T) :-
  min_height(N, H1),
  max_height(N, H2),
  between(H1, H2, H),
  hbal_tree(H, T),
  node_count(T, N).

min_height(N, H) :-
  H is 1 + floor(log(N) / log(2)).

count_hbal_trees(N, C) :- 
  setof(T, hbal_tree_nodes(N, T), S), 
  length(S, C).

count_leaves(nil, 0).
count_leaves(t(_E, nil, nil), 1) :- !.
count_leaves(t(_E, L, R), N) :-
  N #= NL + NR,
  count_leaves(L, NL),
  count_leaves(R, NR).

leaves(nil, []).
leaves(t(E, nil, nil), [E]) :- !.
leaves(t(_E, L, R), C) :-
  leaves(L, CL),
  leaves(R, CR),
  append(CL, CR, C).

internal(nil, []).
internal(t(_E, nil, nil), []) :- !.
internal(t(E, L, R), C) :-
  internal(L, CL),
  internal(R, CR),
  append(CL, [E|CR], C).

atlevel(nil, _, []).
atlevel(_T, 0, []).
atlevel(t(E, _L, _R), 1, [E]).
atlevel(t(_E, L, R), N, A) :-
  N #> 1,
  N1 #= N - 1,
  atlevel(L, N1, AL),
  atlevel(R, N1, AR),
  append(AL, AR, A).
