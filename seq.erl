-module(seq).

%%%%
 %% @(#)seqbdd.erl
 %%
 %% Copyright 2011, Shuhei Denzumi, all rights reserved.
 %%
 %% This file contains an implementation of the data structure and algorithm "SeqBDD".
 %%
 %% This software may be used freely for any purpose. However, when distributed,
 %% the original source must be clearly stated, and, when the source code is
 %% distributed, the copiright notice must be retained and any alterations in
 %% the code must be clearly marked. No warranty is given regarding the quality
 %% of this software.
%%%%


-export([read/1, read/2, write/2, line_write/2]).
-export([sigma/1]).
-export([filter/1]).
-export([n_gram/3]).
-export([read_substring/3]).
-export([read_except_substring/4]).
-export([read_except/2, read_except/3]).
-export([read_lowercase_substring/3]).
-export([read_lowercase/1, read_lowercase/2]).
-export([reads/1, reads/2]).
-export([random/2]).
-export([randoms/3, unique_randoms/3]).
-export([weighted_random/4]).
-export([random_select/2]).
-export([repeat/2]).
-export([all_reverse/1]).
-export([longer/2]).
-export([fibonacci/1]).
-export([worst/1]).
-export([list_projection/2]).
-export([sep/2, trunc/2]).
-export([set/1, hash/3, key/3]).
-export([add/2]).

-export([gen/1]).




read(Filename) ->
    read(Filename, 1 bsl 63).
read(Filename, Length) ->
    {_, File} = file:open(Filename, [read, raw, {read_ahead, 8096}]),
    read(File, Length, []).
read(File, 0, Rseq) ->
    file:close(File),
    lists:reverse(Rseq);
read(File, Length, Rseq) ->
    Result = file:read(File, 1),
    case Result of
      eof ->
	    lists:reverse(Rseq);
      %{_, [10]} ->
	    %read(File, Length, Rseq);
      %{_, [13]} ->
	    %read(File, Length, Rseq);
      {_, [C]} ->
	    read(File, Length-1, [C|Rseq])
    end.


read_substring(Filename, Position, Length) ->
    {_, File} = file:open(Filename, [read, raw, {read_ahead, 8096}]),
    read_substring(File, Position, Length, []).

read_substring(_, _, 0, Rsequence) ->
    lists:reverse(Rsequence);
read_substring(File, 0, Length, Rsequence) ->
    Result = file:read(File, 1),
    case Result of
      eof ->
	    lists:reverse(Rsequence);
      {_, [Character]} ->
	    read_substring(File, 0, Length - 1, [Character|Rsequence])
    end;
read_substring(File, Position, Length, Rsequence) ->
    Result = file:read(File, 1),
    case Result of
      eof ->
	    [];
      {_, [_]} ->
	    read_substring(File, Position - 1, Length, Rsequence)
    end.
    


write(Filename, Data) ->
  {B, O} = file:open(Filename, write),
  case B of
    ok ->
      file:write(O, Data);
    error ->
      0
  end.


line_write(Filename, Data) ->
  {B, O} = file:open(Filename, write),
  case B of
    ok ->
      line_write(O, Data, 32);
    error ->
      0
  end.

line_write(O, [], _) ->
  file:write(O, "\n");
line_write(O, [S], _) ->
%io:fwrite("~w\n", [S]),
  file:write(O, S),
  file:write(O, "\n");
line_write(O, [S|Ss], Delimiter) ->
  %io:fwrite("~w ", [S]),
  file:write(O, S),
  file:write(O, [Delimiter]),
  line_write(O, Ss, Delimiter).


sigma(L) ->
  ets:new(tmp, [private, named_table]),
  recsigma(L),
  N = length(ets:tab2list(tmp)),
  ets:delete(tmp),
  N.

recsigma([]) ->
  ok;
recsigma([C|Cs]) ->
  ets:insert(tmp, {C,C}),
  recsigma(Cs).


filter([]) ->
  [];
filter([C|Cs]) ->
  if
    (48 =< C) and (C =< 57) -> [C|filter(Cs)];
    (65 =< C) and (C =< 90) -> [C+32|filter(Cs)];
    (97 =< C) and (C =< 122) -> [C|filter(Cs)];
    true -> [32|filter(Cs)]
  end.


n_gram(Infile, Outfile, N) ->
  %io:fwrite("INPUT: ~w", [Infile]),
  %S = read(Infile),
  %io:fwrite("S is OK\n", []),
  L = seq:sep(seq:filter(seq:read(Infile)), [32]),
  file:close(Infile),
  io:fwrite("L is length ~w\n", [length(L)]),
  {_, Out} = file:open(Outfile, write),
  n_gram(Out, L, N, 32).

n_gram(Out, [], _, _) ->
  file:close(Out),
  ok;
n_gram(Out, L, N, Delimiter) ->
  line_write(Out, lists:sublist(L, N), Delimiter),
  %io:fwrite("~w\n", [lists:sublist(L, N)]),
  %io:fwrite("~w ~w\n", [length(lists:sublist(L, N)), length(lists:nthtail(1,L))]),
  if
    length(L) =< N -> ok;
    true ->
      n_gram(Out, lists:nthtail(1, L), N, Delimiter)
  end.
  



in(_, []) ->
    false;
in(Item, [Element|Elements]) ->
    case Element of
      Item ->
	    true;
      _ ->
	    in(Item, Elements)
    end.


read_except_substring(Filename, Stoplist, Position, Length) ->
    {_, File} = file:open(Filename, [read, raw, {read_ahead, 8096}]),
    read_except_substring(File, Stoplist, Position, Length, []).

read_except_substring(_, _, _, 0, Rsequence) ->
    lists:reverse(Rsequence);
read_except_substring(File, Stoplist, 0, Length, Rsequence) ->
    Result = file:read(File, 1),
    case Result of
      eof ->
	    lists:reverse(Rsequence);
      {_, [Character]} ->
            In = in(Character, Stoplist),
            if
              In ->
		    read_except_substring(File, Stoplist, 0, Length, Rsequence);
              true ->
                    read_except_substring(File, Stoplist, 0, Length - 1, [Character|Rsequence])
            end
    end;
read_except_substring(File, Stoplist, Position, Length, Rsequence) ->
    Result = file:read(File, 1),
    case Result of
      eof ->
	    [];
      {_, [_]} ->
	    read_except_substring(File, Stoplist, Position - 1, Length, Rsequence)
    end.


read_except(Filename, Stoplist) ->
    read_except(Filename, Stoplist, 1 bsl 63).

read_except(Filename, Stoplist, Length) ->
    read_except(Filename, Stoplist, Length).


read_lowercase_substring(Filename, Position, Length) ->
    {_, File} = file:open(Filename, [read, raw, {read_ahead, 8096}]),
    read_lowercase_substring(File, Position, Length, []).

read_lowercase_substring(_, _, 0, Rsequence) ->
    lists:reverse(Rsequence);
read_lowercase_substring(File, 0, Length, Rsequence) ->
    Result = file:read(File, 1),
    case Result of
      eof ->
	    lists:reverse(Rsequence);
      {_, [Character]} ->
	    if
              64 < Character, Character < 91 ->
		    read_lowercase_substring(File, 0, Length - 1, [Character + 32|Rsequence]);
	      96 < Character, Character < 123 ->
		    read_lowercase_substring(File, 0, Length - 1, [Character|Rsequence]);
	      true ->
		    read_lowercase_substring(File, 0, Length, Rsequence)
            end
    end;
read_lowercase_substring(File, Position, Length, Rsequence) ->
    Result = file:read(File, 1),
    case Result of
      eof ->
	    [];
      {_, [Character]} ->
	    if
              64 < Character, Character < 91; 96 < Character, Character < 123 ->
		    read_lowercase_substring(File, Position - 1, Length, Rsequence);
	      true ->
		    read_lowercase_substring(File, Position, Length, Rsequence)
            end
    end.


read_lowercase(Filename) ->
    read_lowercase(Filename, 1 bsl 63).

read_lowercase(Filename, Length) ->
    read_lowercase_substring(Filename, 0, Length).


reads(Filename) ->
    reads(Filename, 1 bsl 63).
reads(Filename, Number) ->
    {_, File} = file:open(Filename, [read, raw, {read_ahead, 8096}]),
    reads(File, Number, [], []).
reads(File, 0, _, Rseqs) ->
    file:close(File),
    lists:reverse(Rseqs);
reads(File, Number, Rseq, Rseqs) ->
    Result = file:read(File, 1),
    case Result of
      eof ->
	    file:close(File),
	    if
              Rseq =/= [] ->
		    lists:reverse([lists:reverse(Rseq)|Rseqs]);
	      true ->
		    lists:reverse(Rseqs)
            end;
      {_, [10]} ->
	    if
              Rseq =/= [] ->
		    reads(File, Number - 1, [], [lists:reverse(Rseq)|Rseqs]);
	      true ->
		    reads(File, Number, [], Rseqs)
            end;
      {_, [13]} ->
	    if
              Rseq =/= [] ->
		    reads(File, Number - 1, [], [lists:reverse(Rseq)|Rseqs]);
	      true ->
		    reads(File, Number, [], Rseqs)
            end;
      {_, [C]} ->
	    reads(File, Number, [C|Rseq], Rseqs)
    end.




random(_, 0) ->
    [];
random(Domainsize, Length) ->
    [random:uniform(Domainsize)+64|random(Domainsize, Length - 1)].


randoms(_, _, 0) ->
    [];
randoms(Domainsize, Length, Number) ->
    [random(Domainsize, Length)|randoms(Domainsize, Length, Number - 1)].


unique_randoms(_, _, 0) ->
    [];
unique_randoms(Domainsize, Length, Number) ->
    [random(Domainsize, Length) ++ [-256 * Number]|unique_randoms(Domainsize, Length, Number - 1)].



weighted_random(Domainsize, Probability, Power, Length) ->
    weighted_random(1 bsl 32, Domainsize, Probability, Power, Length, []).

weighted_random(_, _, _, _, 0, Sequence) ->
    Sequence;
weighted_random(Width, Domainsize, Probability, Power, Length, Sequence) ->
    Item = random:uniform(Domainsize) - 1,
    Result = Probability * math:pow((Domainsize - Item) / Domainsize, Power),
    Random = random:uniform(Width) / Width,
    if
      Result >= Random ->
	    weighted_random(Width, Domainsize, Probability, Power, Length-1, [Item+65|Sequence]);
      true ->
	    weighted_random(Width, Domainsize, Probability, Power, Length, Sequence)
    end.


random_select(Domainlist, Length) ->
    random_select(array:from_list(Domainlist), length(Domainlist), Length, []).

random_select(_, _, 0, Sequence) ->
    Sequence;
random_select(Domainarray, Domainsize, Length, Tmpsequence) ->
    random_select(Domainarray, Domainsize, Length - 1, [array:get(random:uniform(Domainsize) - 1, Domainarray)|Tmpsequence]).


repeat(_, 0) ->
    [];
repeat(Sequence, Time) ->
    Sequence ++ repeat(Sequence, Time-1).


all_reverse([]) ->
    [];
all_reverse([Sequence|Sequences]) ->
    [lists:reverse(Sequence)|all_reverse(Sequences)].


longer([], _) ->
    [];
longer([Sequence|Sequences], Min_length) ->
    if
      length(Sequence) < Min_length ->
	    longer(Sequences, Min_length);
      true ->
	    [Sequence|longer(Sequences, Min_length)]
    end.


fibonacci(N) ->
    ets:new(fibonacci, [private, named_table]),
    Sequence = fib(N),
    ets:delete(fibonacci),
    erlang:garbage_collect(),
    Sequence.

fib(0) ->
    "";
fib(1) ->
    "A";
fib(2) ->
    "B";
fib(N) ->
    Object = ets:lookup(fibonacci, N),
    case Object of
      [] ->
	    Sequence = fib(N - 2) ++ fib(N - 1),
	    ets:insert(fibonacci, {N, Sequence}),
	    Sequence;
      [{_, Sequence}] ->
	    Sequence
    end.


worst(0) ->
    [];
worst(1) ->
    "A";
worst(2) ->
    "BA";
worst(Length) ->
    worst(Length - 1, "B").

worst(1, Sequence) ->
    "A" ++ Sequence;
worst(Length, Sequence) ->
    worst(Length - 1, "C" ++ Sequence).


list_projection(Inputs, Function) ->
    list_projection(Inputs, Function, []).

list_projection([], _, Rresults) ->
    lists:reverse(Rresults);
list_projection([X|Xs], Function, Rresults) ->
    list_projection(Xs, Function, [Function(X)|Rresults]).


sep(S, D) ->
  sep(S, D, []).

sep([], _, Rseq) ->
  case Rseq of
    [] ->
      [];
    _ ->
      [lists:reverse(Rseq)]
  end;
sep([C|Cs], D, Rseq) ->
  I = lists:member(C, D),
  if
    I ->
      case Rseq of
        [] ->
          sep(Cs, D, []);
        _ ->
          [lists:reverse(Rseq)|sep(Cs, D, [])]
      end;
    true ->
      sep(Cs, D, [C|Rseq])
  end.


trunc([], _) ->
  [];
trunc(L, H) ->
  [lists:sublist(L, H)|trunc(tl(L), H)].


set([]) ->
  [];
set([C]) ->
  [C];
set([C|[C|Cs]]) ->
  set([C|Cs]);
set([C|Cs]) ->
  [C|set(Cs)].


hash(X, N1, N0) ->
  erlang:list_to_binary(hashx(X, N1, N0)).

hashx(0, N1, N0) ->
  hash1(N1, N0);
hashx(X, N1, N0) ->
  L = X bsr 8,
  R = X band 255,
  [R|hashx(L, N1, N0)].

hash1(0, N0) ->
  hash0(N0);
hash1(N1, N0) ->
  L = N1 bsr 8,
  R = N1 band 255,
  [R|hash1(L, N0)].

hash0(0) ->
  [];
hash0(N0) ->
  L = N0 bsr 8,
  R = N0 band 255,
  [R|hash0(L)].


key(X, N1, N0) ->
  ((X band 255) bsl 56 )bor ((N1 band 268435455) bsl 28) bor (N0 band 268435455).


add([], L1) ->
  L1;
add(L0, []) ->
  L0;
add([V0|V0s], [V1|V1s]) ->
  [V0+V1|add(V0s, V1s)].


gen(0) ->
    [];
gen(Length) ->
  B = random:uniform(4),
  case B of
    1 ->
      "A" ++ gen(Length - 1);
    2 ->
      "C" ++ gen(Length - 1);
    3 ->
      "G" ++ gen(Length - 1);
    4 ->
      "T" ++ gen(Length - 1)
  end.

