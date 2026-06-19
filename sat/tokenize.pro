:- module(tokenize, [tokenize/2, bool_op/2]).

tokenize(String, Tokens) :-
  string_chars(String, Chars),
  tokenize_chars(Chars, Tokens).

tokenize_chars([], []).
% skip spaces
tokenize_chars([C|Cs], Tokens) :-
  char_type(C, space), !,
  tokenize_chars(Cs, Tokens).
% recognize ()
tokenize_chars([C|Cs], [Token|Rest]) :-
  member(C, ['(', ')']), !,
  atom_chars(Token, [C]),
  tokenize_chars(Cs, Rest).
% recognize symbols
tokenize_chars(Chars, [Op|Rest]) :-
  find_symbol(Chars, Op, Remainder), !,
  tokenize_chars(Remainder, Rest).  
% recognize variables
tokenize_chars([C|Cs], [var(Var)|Rest]) :-
  char_type(C, alnum), !,
  consume_alnum([C|Cs], VarChars, Remainder),
  atom_chars(Var, VarChars),
  tokenize_chars(Remainder, Rest).

% recognize symbols by longest match
find_symbol(Chars, Op, Remainder) :-
  findall(Len-Atom,
    (bool_op(Atom, _),
      atom_chars(Atom, OpChars),
      append(OpChars, _, Chars),
      length(OpChars, Len)),
    Matches),
  keysort(Matches, Sorted),
  reverse(Sorted, [_ - Op|_]),
  atom_chars(Op, OpChars),
  append(OpChars, Remainder, Chars).  

% aggregate alnum characters
consume_alnum([C|Cs], [C|T], Rest) :-
  char_type(C, alnum), !,
  consume_alnum(Cs, T, Rest).
consume_alnum(Rest, [], Rest).

% symbol spellings for tokenizer
bool_op('->', impl). bool_op('=>', impl).
bool_op('<->', equiv). bool_op('<=>', equiv).
bool_op('or', or). bool_op('OR', or). bool_op('|', or). bool_op('||', or).
bool_op('xor', xor). bool_op('XOR', xor). bool_op('^', xor).
bool_op('and', and). bool_op('AND', and). bool_op('&', and). bool_op('&&', and).
bool_op('not', not). bool_op('NOT', not). bool_op('!', not). bool_op('~', not).
