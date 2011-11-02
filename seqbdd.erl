-module(seqbdd).

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

-export([exp/2, exps/3, info/1, infop/1]).
-export([read_go/1, read_go/2]).
-export([random_go/2]).
-export([weighted_random_go/4]).
-export([repeat_go/2]).
-export([fibonacci_go/1]).
-export([worst_go/1]).
-export([set/0, set_table/0, delete/0, delete_table/0, reset/0]).
-export([node/1]).
-export([clean/1, clean_build_subword/1]).
-export([save/1, free/1]).
-export([garbage_collection/0, garbage_collection/1]).
-export([sufdd/1, subseqdd/1, clean_sufdd/1]).
-export([mulsufdd/1, multisufdd/1]).
-export([build/1, build_prefix/1, build_subword/1, online_build_subword/1, naive_online_build_subword/1]).
-export([multi_build/1, multi_build_once/1, multi_build_once_prefix/1, multi_build_subword/1]).
-export([id_multi_build_subword/1, id_search/2]).
-export([clean_build_subseq/1, cacheless_build_subseq/1]).
-export([dc_build_subseq/1]).
-export([online_build_subseq/1, online_frequent_build_subseq/1]).
-export([frequent_build_subseqs/1]).
-export([frequent_build_subword/1]).
-export([store/1]).
-export([negation/1]).
-export([union/2, intersect/2, minus/2, exclusive_or/2]).
-export([all_node/1]).
-export([multi_union_subword/1]).
-export([all_setoperation/2]).
-export([product/2]).
-export([reverse/1]).
-export([in/2]).
-export([sub/2]).
-export([contain_subseq/2, contain_substr/2]).
-export([subword_union/2]).
-export([add/2, subtract/2]).
-export([search/2, search_node/2]).
-export([star_build_subword/1, miss_search/3]).
-export([position_build_subword/1]).
-export([print/1, printfile/2]).
-export([seqbdd2file/2]).
-export([count/1, multi_count/1, tree_count/1, death_count/1]).
-export([path/1]).
-export([depth/1, shallowness/1]).
-export([number/2, much/3,much/2]).
-export([longest/1, shortest/1]).
-export([character/1]).
-export([decompress/1]).
-export([random/1]).
-export([shorter/2, longer/2, just/2]).
-export([position/2]).
-export([frequency/2]).
-export([more/2, less/2, equal/2]).
-export([suffix/2]).

-export([psdd/1, ssdd/1, fsdd/1, fsdd_dfa/1, fsdd_rec0/1, fsdd_once/1]).%fsdd_rec/1

-export([cacheless_build_subword/1]).
-export([cacheless_union/2, cacheless_intersect/2, cacheless_minus/2]).
-export([cacheless_subword_union/2]).
-export([cache_add/2]).

-export([bool_add/2]).
-export([mining_intersect/2]).

-export([anymiss/1, miss/2]).
-export([recognize/2]).
-export([window/2]).
-export([newid/0]).
-export([occur_sufdd/1, occur_union/2, occur_search/2]).
-export([occur_intersect/2]).
-export([occurence_union/2]).
-export([occur_anymiss/1, occur_miss/2]).
-export([occurence_search/2]).
-export([window_search/4]).
-export([window_miss/4]).
-export([descendant/1]).
-export([s_maximal/2]).
-export([maximal/2, maximal/3]).
-export([super_maximal/2, super_maximal/3]).

-export([list_union_d_order/2]).


-export([p_search/2]).
-export([p_subword_union/3]).
-export([p_sufdd/1]).
-export([p_union/2]).
-export([p_w_miss/4]).
-export([p_id_union/2]).
-export([db_create/4]).

-export([p_w_miss_a/3]).
-export([p_search_a/2]).
-export([p_search_an/2]).
-export([db_create_a/3]).



-define(CACHE, true).
-define(BITWIDTH, (64)).
-define(CLEANNUMBER, (1 bsl 21)).
-define(CLEANTIME, (1 bsl 10)).

-define(I2A(X), list_to_atom(integer_to_list(X))).
-define(A2I(X), list_to_integer(atom_to_list(X))).
-define(SET(X), sets:to_list(sets:from_list(X))).

exps(_, _, Num) when Num =< 0 ->
  [];
exps(S, N, Num) ->
  L = exps(S, N, Num - 1, exp(S, N)),
  lists:map(fun(V) -> V / Num end, L).

exps(_, _, 0, R) ->
  R;
exps(S, N, Num, R) ->
  exps(S, N, Num - 1, seq:add(R, exp(S, N))).

exp(R, Num) when not is_list(R) ->
    exp([R], Num);
exp([R|Rs], Num) when not is_list(R) ->
    exp([[R]|Rs], Num);
exp(S, Num) ->
    I = ets:info(nodememory),
    case I of
      undefined ->
        set();
      _ ->
        reset()
    end,
    case Num of
      1 ->
        %io:fwrite("|S| = ~w\t||S|| =  ~w\n", [length(S), lists:sum(lists:map(fun(W) -> length(W) end, S))]),
        io:fwrite(" SDD FOR S\n", []),
        {TSDD, SDD} = timer:tc(seqbdd, multi_build_once, [S]),
        infop(SDD),
        %io:fwrite(" SDD TIME : ~w [s]\n", [TSDD / 1000000.0]),
        {TPSDD, PSDD} = timer:tc(seqbdd, psdd, [SDD]),
        %io:fwrite("PSDD FOR S\n", []),
        %infop(PSDD),
        %io:fwrite("PSDD TIME : ~w [s]\n", [TPSDD / 1000000.0]),
        {TVN, VN} = timer:tc(seqbdd, all_node, [PSDD]),
        %io:fwrite(" GET TIME : ~w [s]\n", [TVN / 1000000.0]),
        {TFSDD, FSDD} = timer:tc(seqbdd, multi_union_subword, [VN]),%timer:tc(seqbdd, fsdd, [SDD]), %timer:tc(seqbdd, multi_union_subword, [VN]),
        io:fwrite("FSDD FOR S\n", []),
        infop(FSDD),
        %io:fwrite("FSDD TIME : ~w [s]\n", [TFSDD / 1000000.0]),
        %io:fwrite(" ALL TIME : ~w [s]\n", [(TSDD + TPSDD + TVN + TFSDD) / 1000000.0]),
        %io:fwrite("~w ~w ~w ~w ~w ~w ~w\n", [TSDD / 1000000.0, 0, TVN / 1000000.0, TFSDD / 1000000.0, TPSDD / 1000000.0, 0, (TSDD + TPSDD + TVN + TFSDD) / 1000000.0]),
        [TSDD / 1000000.0, 0, TVN / 1000000.0, TFSDD / 1000000.0, TPSDD / 1000000.0, 0, (TSDD + TPSDD + TVN + TFSDD) / 1000000.0];
        %FSDD;
      2 ->
        io:fwrite("2 EXPERIMENT\n", []),
        
        {T1, N1} = timer:tc(seqbdd, multi_build_once, [seq:sep(seq:read("bi.paper1.txt"), "\r\n")]),%timer:tc(seqbdd, fsdd, [seq:sep(seq:read("bi.paper1"), "\r\n")]),
        {T2, N2} = timer:tc(seqbdd, multi_build_once, [seq:sep(seq:read("bi.paper2.txt"), "\r\n")]),%timer:tc(seqbdd, fsdd, [seq:sep(seq:read("bi.paper2"), "\r\n")]),
        {T3, N3} = timer:tc(seqbdd, multi_build_once, [seq:sep(seq:read("bi.paper3.txt"), "\r\n")]),%timer:tc(seqbdd, fsdd, [seq:sep(seq:read("bi.paper3"), "\r\n")]),
        {T4, N4} = timer:tc(seqbdd, multi_build_once, [seq:sep(seq:read("bi.paper4.txt"), "\r\n")]),%timer:tc(seqbdd, fsdd, [seq:sep(seq:read("bi.paper4"), "\r\n")]),
        {T5, N5} = timer:tc(seqbdd, multi_build_once, [seq:sep(seq:read("bi.paper5.txt"), "\r\n")]),%timer:tc(seqbdd, fsdd, [seq:sep(seq:read("bi.paper5"), "\r\n")]),
        {T6, N6} = timer:tc(seqbdd, multi_build_once, [seq:sep(seq:read("bi.paper6.txt"), "\r\n")]),%timer:tc(seqbdd, fsdd, [seq:sep(seq:read("bi.paper6"), "\r\n")]),
        io:fwrite("1 CLEAR\n", []),
        
        {T12, N12} = timer:tc(seqbdd, union, [N1, N2]),
        {T13, N13} = timer:tc(seqbdd, union, [N1, N3]),
        {T14, N14} = timer:tc(seqbdd, union, [N1, N4]),
        {T15, N15} = timer:tc(seqbdd, union, [N1, N5]),
        {T16, N16} = timer:tc(seqbdd, union, [N1, N6]),
        {T23, N23} = timer:tc(seqbdd, union, [N2, N3]),
        {T24, N24} = timer:tc(seqbdd, union, [N2, N4]),
        {T25, N25} = timer:tc(seqbdd, union, [N2, N5]),
        {T26, N26} = timer:tc(seqbdd, union, [N2, N6]),
        {T34, N34} = timer:tc(seqbdd, union, [N3, N4]),
        {T35, N35} = timer:tc(seqbdd, union, [N3, N5]),
        {T36, N36} = timer:tc(seqbdd, union, [N3, N6]),
        {T45, N45} = timer:tc(seqbdd, union, [N4, N5]),
        {T46, N46} = timer:tc(seqbdd, union, [N4, N6]),
        {T56, N56} = timer:tc(seqbdd, union, [N5, N6]),
        io:fwrite("2 CLEAR\n", []),
        
        {T123, N123} = timer:tc(seqbdd, union, [N12, N3]),
        {T124, N124} = timer:tc(seqbdd, union, [N12, N4]),
        {T125, N125} = timer:tc(seqbdd, union, [N12, N5]),
        {T126, N126} = timer:tc(seqbdd, union, [N12, N6]),
        {T134, N134} = timer:tc(seqbdd, union, [N13, N4]),
        {T135, N135} = timer:tc(seqbdd, union, [N13, N5]),
        {T136, N136} = timer:tc(seqbdd, union, [N13, N6]),
        {T145, N145} = timer:tc(seqbdd, union, [N14, N5]),
        {T146, N146} = timer:tc(seqbdd, union, [N14, N6]),
        {T156, N156} = timer:tc(seqbdd, union, [N15, N6]),
        {T234, N234} = timer:tc(seqbdd, union, [N23, N4]),
        {T235, N235} = timer:tc(seqbdd, union, [N23, N5]),
        {T236, N236} = timer:tc(seqbdd, union, [N23, N6]),
        {T245, N245} = timer:tc(seqbdd, union, [N24, N5]),
        {T246, N246} = timer:tc(seqbdd, union, [N24, N6]),
        {T256, N256} = timer:tc(seqbdd, union, [N25, N6]),
        {T345, N345} = timer:tc(seqbdd, union, [N34, N5]),
        {T346, N346} = timer:tc(seqbdd, union, [N34, N6]),
        {T356, N356} = timer:tc(seqbdd, union, [N35, N6]),
        {T456, N456} = timer:tc(seqbdd, union, [N45, N6]),
        io:fwrite("3 CLEAR\n", []),
        
        {T1234, N1234} = timer:tc(seqbdd, union, [N123, N4]),
        {T1235, N1235} = timer:tc(seqbdd, union, [N123, N5]),
        {T1236, N1236} = timer:tc(seqbdd, union, [N123, N6]),
        {T1245, N1245} = timer:tc(seqbdd, union, [N124, N5]),
        {T1246, N1246} = timer:tc(seqbdd, union, [N124, N6]),
        {T1256, N1256} = timer:tc(seqbdd, union, [N125, N6]),
        {T1345, N1345} = timer:tc(seqbdd, union, [N134, N5]),
        {T1346, N1346} = timer:tc(seqbdd, union, [N134, N6]),
        {T1356, N1356} = timer:tc(seqbdd, union, [N135, N6]),
        {T1456, N1456} = timer:tc(seqbdd, union, [N145, N6]),
        {T2345, N2345} = timer:tc(seqbdd, union, [N234, N5]),
        {T2346, N2346} = timer:tc(seqbdd, union, [N234, N6]),
        {T2356, N2356} = timer:tc(seqbdd, union, [N235, N6]),
        {T2456, N2456} = timer:tc(seqbdd, union, [N245, N6]),
        {T3456, N3456} = timer:tc(seqbdd, union, [N345, N6]),
        io:fwrite("4 CLEAR\n", []),
        
        {T12345, N12345} = timer:tc(seqbdd, union, [N1234, N5]),
        {T12346, N12346} = timer:tc(seqbdd, union, [N1234, N6]),
        {T12356, N12356} = timer:tc(seqbdd, union, [N1235, N6]),
        {T12456, N12456} = timer:tc(seqbdd, union, [N1245, N6]),
        {T13456, N13456} = timer:tc(seqbdd, union, [N1345, N6]),
        {T23456, N23456} = timer:tc(seqbdd, union, [N2345, N6]),
        io:fwrite("5 CLEAR\n", []),
        
        {T123456, N123456} = timer:tc(seqbdd, union, [N12345, N6]),
        io:fwrite("6 CLEAR\n", []),
        
        L1 = [N1, N2, N3, N4, N5, N6],
        L2 = [N12, N13, N14, N15, N16, N23, N24, N25, N26, N34, N35, N36, N45, N46, N56],
        L3 = [N123, N124, N125, N126, N134, N135, N136, N145, N146, N156, N234, N235, N236, N245, N246, N256, N345, N346, N356, N456],
        L4 = [N1234, N1235, N1236, N1245, N1246, N1256, N1345, N1346, N1356, N1456, N2345, N2346, N2356, N2456, N3456],
        L5 = [N12345, N12346, N12356, N12456, N13456, N23456],
        L6 = [N123456],
        L0 = L1 ++ L2 ++ L3 ++ L4 ++ L5 ++ L6,
        
        S1 = lists:sum([T1, T2, T3, T4, T5, T6]),
        S2 = lists:sum([T12, T13, T14, T15, T16, T23, T24, T25, T26, T34, T35, T36, T45, T46, T56]),
        S3 = lists:sum([T123, T124, T125, T126, T134, T135, T136, T145, T146, T156, T234, T235, T236, T245, T246, T256, T345, T346, T356, T456]),
        S4 = lists:sum([T1234, T1235, T1236, T1245, T1246, T1256, T1345, T1346, T1356, T1456, T2345, T2346, T2356, T2456, T3456]),
        S5 = lists:sum([T12345, T12346, T12356, T12456, T13456, T23456]),
        S6 = lists:sum([T123456]),
        S0 = lists:sum([S1, S2, S3, S4, S5, S6]),
        
        infop(N123456),
        V1 = lists:map(fun(N) -> count(N) end, L1),
        V2 = lists:map(fun(N) -> count(N) end, L2),
        V3 = lists:map(fun(N) -> count(N) end, L3),
        V4 = lists:map(fun(N) -> count(N) end, L4),
        V5 = lists:map(fun(N) -> count(N) end, L5),
        V6 = lists:map(fun(N) -> count(N) end, L6),
        V0 = lists:map(fun(N) -> count(N) end, L0),
        
        W1 = multi_count(L1),
        W2 = multi_count(L2),
        W3 = multi_count(L3),
        W4 = multi_count(L4),
        W5 = multi_count(L5),
        W6 = multi_count(L6),
        W0 = multi_count(L0),
        
        io:fwrite("1\t", []),
        infop(N1),
        io:fwrite("2\t", []),
        infop(N2),
        io:fwrite("3\t", []),
        infop(N3),
        io:fwrite("4\t", []),
        infop(N4),
        io:fwrite("5\t", []),
        infop(N5),
        io:fwrite("6\t", []),
        infop(N6),
        
        io:fwrite("12\t", []),
        infop(N12),
        io:fwrite("13\t", []),
        infop(N13),
        io:fwrite("14\t", []),
        infop(N14),
        io:fwrite("15\t", []),
        infop(N15),
        io:fwrite("16\t", []),
        infop(N16),
        io:fwrite("23\t", []),
        infop(N23),
        io:fwrite("24\t", []),
        infop(N24),
        io:fwrite("25\t", []),
        infop(N25),
        io:fwrite("26\t", []),
        infop(N26),
        io:fwrite("34\t", []),
        infop(N34),
        io:fwrite("35\t", []),
        infop(N35),
        io:fwrite("36\t", []),
        infop(N36),
        io:fwrite("45\t", []),
        infop(N45),
        io:fwrite("46\t", []),
        infop(N46),
        io:fwrite("56\t", []),
        infop(N56),
        
        io:fwrite("123\t", []),
        infop(N123),
        io:fwrite("124\t", []),
        infop(N124),
        io:fwrite("125\t", []),
        infop(N125),
        io:fwrite("126\t", []),
        infop(N126),
        io:fwrite("134\t", []),
        infop(N134),
        io:fwrite("135\t", []),
        infop(N135),
        io:fwrite("136\t", []),
        infop(N136),
        io:fwrite("145\t", []),
        infop(N145),
        io:fwrite("146\t", []),
        infop(N146),
        io:fwrite("156\t", []),
        infop(N156),
        io:fwrite("234\t", []),
        infop(N234),
        io:fwrite("235\t", []),
        infop(N235),
        io:fwrite("236\t", []),
        infop(N236),
        io:fwrite("245\t", []),
        infop(N245),
        io:fwrite("246\t", []),
        infop(N246),
        io:fwrite("256\t", []),
        infop(N256),
        io:fwrite("345\t", []),
        infop(N345),
        io:fwrite("346\t", []),
        infop(N346),
        io:fwrite("356\t", []),
        infop(N356),
        io:fwrite("456\t", []),
        infop(N456),
        
        io:fwrite("1234\t", []),
        infop(N1234),
        io:fwrite("1235\t", []),
        infop(N1235),
        io:fwrite("1236\t", []),
        infop(N1236),
        io:fwrite("1245\t", []),
        infop(N1245),
        io:fwrite("1246\t", []),
        infop(N1246),
        io:fwrite("1256\t", []),
        infop(N1256),
        io:fwrite("1345\t", []),
        infop(N1345),
        io:fwrite("1346\t", []),
        infop(N1346),
        io:fwrite("1356\t", []),
        infop(N1356),
        io:fwrite("1456\t", []),
        infop(N1456),
        io:fwrite("2345\t", []),
        infop(N2345),
        io:fwrite("2346\t", []),
        infop(N2346),
        io:fwrite("2356\t", []),
        infop(N2356),
        io:fwrite("2456\t", []),
        infop(N2456),
        io:fwrite("3456\t", []),
        infop(N3456),
        
        io:fwrite("12345\t", []),
        infop(N12345),
        io:fwrite("12346\t", []),
        infop(N12346),
        io:fwrite("12356\t", []),
        infop(N12356),
        io:fwrite("12456\t", []),
        infop(N12456),
        io:fwrite("13456\t", []),
        infop(N13456),
        io:fwrite("23456\t", []),
        infop(N23456),
        
        io:fwrite("123456\t", []),
        infop(N123456),
        
        io:fwrite("1 TIME ~w\n", [S1]),
        io:fwrite("2 TIME ~w\n", [S2]),
        io:fwrite("3 TIME ~w\n", [S3]),
        io:fwrite("4 TIME ~w\n", [S4]),
        io:fwrite("5 TIME ~w\n", [S5]),
        io:fwrite("6 TIME ~w\n", [S6]),
        io:fwrite("0 TIME ~w\n", [S0]),
        io:fwrite("\n", []),
        io:fwrite("1 NODE ~w\n", [V1]),
        io:fwrite("2 NODE ~w\n", [V2]),
        io:fwrite("3 NODE ~w\n", [V3]),
        io:fwrite("4 NODE ~w\n", [V4]),
        io:fwrite("5 NODE ~w\n", [V5]),
        io:fwrite("6 NODE ~w\n", [V6]),
        io:fwrite("0 NODE ~w\n", [V0]),
        io:fwrite("\n", []),
        io:fwrite("1 SUMS ~w\n", [lists:sum(V1)]),
        io:fwrite("2 SUMS ~w\n", [lists:sum(V2)]),
        io:fwrite("3 SUMS ~w\n", [lists:sum(V3)]),
        io:fwrite("4 SUMS ~w\n", [lists:sum(V4)]),
        io:fwrite("5 SUMS ~w\n", [lists:sum(V5)]),
        io:fwrite("6 SUMS ~w\n", [lists:sum(V6)]),
        io:fwrite("0 SUMS ~w\n", [lists:sum(V0)]),
        io:fwrite("\n", []),
        io:fwrite("1 SIZE ~w\n", [W1]),
        io:fwrite("2 SIZE ~w\n", [W2]),
        io:fwrite("3 SIZE ~w\n", [W3]),
        io:fwrite("4 SIZE ~w\n", [W4]),
        io:fwrite("5 SIZE ~w\n", [W5]),
        io:fwrite("6 SIZE ~w\n", [W6]),
        io:fwrite("0 SIZE ~w\n", [W0]),
        %L0;
        [S1, S2, S3, S4, S5, S6, S0];
      _ ->
        io:fwrite("NOT REGISTERED EXPERIMENT.\n", [])
    end.


info(0) ->
  {1, 0, 0};
info(R) ->
  C = count(R),
  {C, C * 2, path(R)}.


infop(R) ->
  {V, E, S} = info(R),
  io:fwrite("|VN| = ~w\t|E| = ~w\t|L| = ~w\n", [V, E, S]).


read_go(Filename) ->
    read_go(Filename, 1 bsl 64).

read_go(Filename, Length) ->
    set_table(),
    online_build_subword(seq:read(Filename, Length)),
    delete_table().


random_go(Domainsize, Length) ->
    set_table(),
    online_build_subword(seq:random(Domainsize, Length)),
    delete_table().

weighted_random_go(Domainsize, Probability, Power, Length) ->
    set_table(),
    online_build_subword(seq:weighted_random(Domainsize, Probability, Power, Length)),
    delete_table().


fibonacci_go(N) ->
    set_table(),
    online_build_subword(seq:fibonacci(N)),
    delete_table().


repeat_go(Sequence, Time) ->
    set_table(),
    online_build_subword(seq:repeat(Sequence, Time)),
    delete_table().


worst_go(Length) ->
    set_table(),
    online_build_subword(seq:worst(Length)),
    delete_table().




set() ->
  set_table().

set_table() ->
    ets:new(uniquetable, [private, named_table]),
    ets:new(nodememory, [private, named_table]),
    ets:insert(uniquetable, {{false, 0, 0}, 0}),
    ets:insert(uniquetable, {{true, 0, 0}, 1}),
    ets:insert(nodememory, {0, {false, 0, 0}}),
    ets:insert(nodememory, {1, {true, 0, 0}}),
    ets:insert(nodememory, {node_number, 1}),
    ets:insert(nodememory, {referenced, []}),
    ets:insert(nodememory, {last_cleannumber, 1}),
    ets:insert(nodememory, {id, -1}),
    ets:new(cache, [private, named_table]),
    ok.

delete() ->
  delete_table().

delete_table() ->
    ets:delete(uniquetable),
    ets:delete(nodememory),
    ets:delete(cache),
    erlang:garbage_collect(),
    ok.


node(N) ->
    Object = ets:lookup(nodememory, N),
    case Object of
      [] ->
        {};
      [{_, Node}] ->
        Node
    end.

reset() ->
  I = ets:info(uniquetable),
  case I of
    undefined ->
      ok;
    _ ->
      delete()
  end,
  set().


store({_, 0, N0}) ->
    N0;
store(Node) ->
    Object = ets:lookup(uniquetable, Node),
    case Object of
      [] ->
	    Number = ets:update_counter(nodememory, node_number, {2, 1}),
	    ets:insert(uniquetable, {Node, Number}),
	    ets:insert(nodememory, {Number, Node}),
	    Number;
      [{_, Number}] ->
	    Number
    end.


clean(Root) when not is_list(Root) ->
  clean([Root]);
clean(Rootlist) ->
    ets:new(tmpuniquetable, [private, named_table]),
    ets:new(tmpnodememory, [private, named_table]),
    ets:insert(tmpuniquetable, {{false, 0, 0}, 0}),
    ets:insert(tmpuniquetable, {{true, 0, 0}, 1}),
    ets:insert(tmpnodememory, {0, {false, 0, 0}}),
    ets:insert(tmpnodememory, {1, {true, 0, 0}}),
    [{_, Nodenumber}] = ets:lookup(nodememory, node_number),
    ets:insert(tmpnodememory, {node_number, Nodenumber}),
    [{_, Referenced}] = ets:lookup(nodememory, referenced),
    ets:insert(tmpnodememory, {referenced, Referenced}),
    [{_, Id}] = ets:lookup(nodememory, id),
    ets:insert(tmpnodememory, {id, Id}),
    ets:insert(tmpnodememory, {last_cleannumber, Nodenumber}),
    lists:foreach(fun(Root) -> copy(Root) end, Rootlist ++ Referenced),
    ets:tab2file(tmpuniquetable, "uniquetable.ets"),
    ets:tab2file(tmpnodememory, "nodememory.ets"),
    ets:delete(tmpuniquetable),
    ets:delete(tmpnodememory),
    ets:delete(uniquetable),
    ets:delete(nodememory),
    ets:delete(cache),
    erlang:garbage_collect(),
    ets:file2tab("uniquetable.ets"),
    ets:file2tab("nodememory.ets"),
    ets:rename(tmpuniquetable, uniquetable),
    ets:rename(tmpnodememory, nodememory),
    ets:new(cache, [private, named_table]),
    ok.

copy(N) ->
    Object = ets:lookup(nodememory, N),
    case Object of
      [] ->
	    0;
      [{_, {X, N1, N0}}] ->
	    ets:delete(nodememory, N),
	    ets:insert(tmpuniquetable, {{X, N1, N0}, N}),
	    ets:insert(tmpnodememory, {N, {X, N1, N0}}),
	    Location = ets:lookup(nodememory, {location, N}),
	    case Location of
	      [] ->
	        ok;
	      [{_, Occur}] ->
	        ets:insert(tmpnodememory, {{location, N}, Occur})
	    end,
	    Frequency = ets:lookup(nodememory, {freq, N}),
	    case Frequency of
	      [] ->
	        ok;
	      [{_, Freq}] ->
	        ets:insert(tmpnodememory, {{freq, N}, Freq})
	    end,
	    copy(N1) + copy(N0) + 1
    end.


save(Rootlist) when is_list(Rootlist) ->
    [{_, Roots}] = ets:lookup(nodememory, referenced),
    ets:insert(nodememory, {referenced, Rootlist ++ Roots}),
    ok;
save(Root) ->
    save([Root]).


free(Rootlist) when is_list(Rootlist) ->
    [{_, Roots}] = ets:lookup(nodememory, referenced),
    ets:insert(nodememory, {referenced, Roots -- Rootlist}),
    ok;
free(Root) ->
    free([Root]).


garbage_collection() ->
    garbage_collection([]).

garbage_collection(Rootlist) when is_list(Rootlist) ->
    [{_, Lastcleannumber}] = ets:lookup(nodememory, last_cleannumber),
    [{_, Nodenumber}] = ets:lookup(nodememory, node_number),
    if
      Nodenumber - Lastcleannumber > ?CLEANNUMBER ->
	    [{_, Referenced}] = ets:lookup(nodememory, referenced),
	    clean(Rootlist ++ Referenced);
      true ->
	    ok
    end;
garbage_collection(Root) ->
    garbage_collection([Root]).


build([]) ->
    1;
build([Item|Items]) ->
    store({Item, build(Items), 0}).


build_prefix([]) ->
    1;
build_prefix([Item|Items]) ->
    store({Item, build_prefix(Items), 1}).
    


sufdd(Sequence) ->
  build_subword(Sequence).


subseqdd(Sequence) ->
  online_build_subseq(Sequence).


clean_sufdd(Sequence) ->
  clean_build_subword(Sequence).


build_subword(Sequence) ->
    build_subword(build_prefix(Sequence), 1).

build_subword(1, Root) ->
    Root;
build_subword(Parent, Tmproot) ->
    Newroot = subword_union(Parent, Tmproot),
    [{_, {_, Child, _}}] = ets:lookup(nodememory, Parent),
    build_subword(Child, Newroot).


online_build_subword(Sequence) ->
    online_build_subword(lists:reverse(Sequence), 1, 0).

online_build_subword([], _, Root) ->
    Root;
online_build_subword([Item|Items], Prefix, Tmproot) ->
    Newprefix = store({Item, Prefix, 1}),
    Newroot = subword_union(Newprefix, Tmproot),
    online_build_subword(Items, Newprefix, Newroot).


naive_online_build_subword(Sequence) ->
    naive_online_build_subword(Sequence, [], 1).

naive_online_build_subword([], _, Root) ->
    Root;
naive_online_build_subword([Item|Items], Rpastsequence, Tmproot) ->
    naive_online_build_subword(Items, [Item|Rpastsequence], naive_build_subword([Item|Rpastsequence], 1, Tmproot)).

naive_build_subword([], _, Root) ->
    Root;
naive_build_subword([Item|Rsequence], Sequenceroot, Tmproot) ->
    Node = {Item, Sequenceroot, 0},
    Object = ets:lookup(uniquetable, {Item, Sequenceroot, 0}),
    case Object of
      [] ->
	    Number = ets:update_counter(nodememory, node_number, {2, 1}),
	    ets:insert(uniquetable, {Node, Number}),
	    ets:insert(nodememory, {Number, Node}),
	    naive_build_subword(Rsequence, Number, union(Number, Tmproot));
      [{_, Number}] ->
	    naive_build_subword(Rsequence, Number, Tmproot)
    end.


multi_build(S) when not is_list(S) ->
    multi_build([S]);
multi_build([S|Ss]) when not is_list(S) ->
    multi_build([[S]|Ss]);
multi_build(L) ->
    multi_build(L, 0).

multi_build([], R) ->
    R;
multi_build([S|Ss], N) ->
    multi_build(Ss, union(N, build(S))).


multi_build_subword(Sequences) ->
    Number = length(Sequences),
    multi_build_subword(seq:all_reverse(Sequences), [], lists:duplicate(Number, 1), [], 1).

multi_build_subword([], [], _, _, Root) ->
    Root;
multi_build_subword([], Nexts, _, Parents, Tmproot) ->
    multi_build_subword(lists:reverse(Nexts), [], lists:reverse(Parents), [], Tmproot);
multi_build_subword([Sequence|Sequences], Nexts, [Child|Children], Parents, Tmproot) ->
    case Sequence of
      [Item|Items] ->
	    Parent = store({Item, Child, 1}),
	    Newroot = subword_union(Parent, Tmproot),
	    multi_build_subword(Sequences, [Items|Nexts], Children, [Parent|Parents], Newroot);
      [] ->
	    multi_build_subword(Sequences, Nexts, Children, Parents, Tmproot)
    end.


multi_build_once(S) when not is_list(S) ->
    multi_build_once([S]);
multi_build_once([S|Ss]) when not is_list(S) ->
    multi_build_once([[S]|Ss]);
multi_build_once(L) ->
    multi_build_once1(seq:set(lists:sort(L))).

multi_build_once1([[]]) ->
  1;
multi_build_once1([[]|[[C|Cs]|Ss]]) ->
  multi_build_once0([[C|Cs]|Ss], C, [], 1);
multi_build_once1([[C|Cs]|Ss]) ->
  multi_build_once0([[C|Cs]|Ss], C, [], 0).

multi_build_once0([], A, As, T) ->
  store({A, multi_build_once1(lists:reverse(As)), T});
multi_build_once0([[A|Bs]|Ss], A, As, T) ->
  multi_build_once0(Ss, A, [Bs|As], T);
multi_build_once0([[B|Bs]|Ss], A, As, T) ->
  store({A, multi_build_once1(lists:reverse(As)), multi_build_once0(Ss, B, [Bs], T)}).


multi_build_once_prefix(S) when not is_list(S) ->
    multi_build_once_prefix([S]);
multi_build_once_prefix([S|Ss]) when not is_list(S) ->
    multi_build_once_prefix([[S]|Ss]);
multi_build_once_prefix(L) ->
    multi_build_once_prefix1(seq:set(lists:sort(L))).

multi_build_once_prefix1([[]]) ->
  1;
multi_build_once_prefix1([[]|[[C|Cs]|Ss]]) ->
  multi_build_once_prefix0([[C|Cs]|Ss], C, []);
multi_build_once_prefix1([[C|Cs]|Ss]) ->
  multi_build_once_prefix0([[C|Cs]|Ss], C, []).

multi_build_once_prefix0([], A, As) ->
  store({A, multi_build_once_prefix1(lists:reverse(As)), 1});
multi_build_once_prefix0([[A|Bs]|Ss], A, As) ->
  multi_build_once_prefix0(Ss, A, [Bs|As]);
multi_build_once_prefix0([[B|Bs]|Ss], A, As) ->
  store({A, multi_build_once_prefix1(lists:reverse(As)), multi_build_once_prefix0(Ss, B, [Bs])}).


id_multi_build_subword(Sequences) ->
    Ids = lists:map(fun(X) -> store({?I2A(X), 1, 1}) end, lists:seq(1, length(Sequences))),
    id_multi_build_subword(seq:all_reverse(Sequences), [], Ids, [], Ids, [], 1).

id_multi_build_subword([], [], _, _, _, _, Root) ->
    Root;
id_multi_build_subword([], Nexts, _, Rid, _, Parents, Tmproot) ->
    id_multi_build_subword(lists:reverse(Nexts), [], lists:reverse(Rid), [], lists:reverse(Parents), [], Tmproot);
id_multi_build_subword([Sequence|Sequences], Nexts, [Id|Ids], Rid, [Child|Children], Parents, Tmproot) ->
    case Sequence of
      [Item|Items] ->
	    Parent = store({Item, Child, Id}),
	    Newroot = subword_union(Parent, Tmproot),
	    id_multi_build_subword(Sequences, [Items|Nexts], Ids, [Id|Rid], Children, [Parent|Parents], Newroot);
      [] ->
	    id_multi_build_subword(Sequences, Nexts, Ids, Rid, Children, Parents, Tmproot)
    end.


id_search(Root, Sequence) ->
    Suffix = search_node(Root, Sequence),
    id_search(Suffix).

id_search(N) when N =< 1 ->
    [];
id_search(N) ->
    [{_, {X, _, N0}}] = ets:lookup(nodememory, N),
    if
      is_atom(X) ->
        [X|id_search(N0)];
      true ->
        id_search(N0)
    end.


clean_build_subseq(Sequence) ->
    clean_build_subseq(lists:reverse(Sequence), 1, 0).

clean_build_subseq([], Root, _) ->
    Root;
clean_build_subseq(Items, Tmproot, Time) when Time >= ?CLEANTIME ->
    clean([Tmproot]),
    clean_build_subseq(Items, Tmproot, 0);
clean_build_subseq([Item|Items], Tmproot, Time) ->
io:format("Another ~p\n", [length(Items)]),
    clean_build_subseq(Items, subword_union(store({Item, Tmproot, 1}), Tmproot), Time + 1).


cacheless_build_subseq(Sequence) ->
    cacheless_build_subseq(lists:reverse(Sequence), 1).

cacheless_build_subseq([], Root) ->
    Root;
cacheless_build_subseq([Item|Items], Tmproot) ->
io:format("Another ~p\n", [length(Items)]),
    cacheless_build_subseq(Items, cacheless_subword_union(store({Item, Tmproot, 1}), Tmproot)).


dc_build_subseq(Sequence) ->
  dc_build_subseq(array:from_list(Sequence), 0, length(Sequence)).

dc_build_subseq(_, K, K) ->
  0;
dc_build_subseq(String, I, J) when I + 1 =:= J ->
  X = array:get(I, String),
  store({X, 1, 1});
dc_build_subseq(String, I, J) ->
  K = I + ((J - I) div 2),
  P = dc_build_subseq(String, I, K),
  Q = dc_build_subseq(String, K, J),
  R = product(P, Q),
  union(Q, R).


online_build_subseq(Sequence) ->
    online_build_subseq(lists:reverse(Sequence), 1).

online_build_subseq([], Root) ->
    Root;
online_build_subseq([Item|Items], Tmproot) ->
    online_build_subseq(Items, subword_union(store({Item, Tmproot, 1}), Tmproot)).


%online_frequent_build_subseq(Sequence) ->
%    online_frequent_build_subseq(lists:reverse(Sequence), 1, lists:duplicate(?BITWIDTH - 1, 0) ++ [1]).
%
%online_frequent_build_subseq([], _, Roots) ->
%    Roots;
%online_frequent_build_subseq([Item|Items], Tmproot, Tmproots) ->
%    Newsubseq = store({Item, Tmproot, 1}),
%    Newroots = add(lists:duplicate(?BITWIDTH - 1, 0) ++ [Newsubseq], Tmproots),
%    online_frequent_build_subseq(Items, union(Newsubseq, Tmproot), Newroots).


online_frequent_build_subseq(Sequence) ->
    online_frequent_build_subseq(lists:reverse(Sequence), lists:duplicate(?BITWIDTH - 1, 0) ++ [1]).

online_frequent_build_subseq([], Roots) ->
    Roots;
online_frequent_build_subseq([Item|Items], Tmproots) ->
    Newsubseqs = new_subseq(Item, Tmproots),
    Newroots = bool_add(Tmproots, Newsubseqs),
    online_frequent_build_subseq(Items, Newroots).

%new_subseq(Item, [Root|[]]) ->
%    [store({Item, Root, 1})];
%new_subseq(Item, [Root|Roots]) ->
%    case Root of
%      0 ->
%	    [0|new_subseq(Item, Roots)];
%      Root ->
%	    [store({Item, Root, 0})|new_subseq(Item, Roots)]
%    end.

new_subseq(Item, [Root|Roots]) ->
    if
      length(Roots) > 0 ->
	    [store({Item, push(0, Root), 0})|new_subseq(Item, Roots)];
      true ->
	    [store({Item, push(1, Root), 1})]
    end.


push(TF, Sink) when Sink =< 1 ->
    TF;
push(TF, N) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    store({X, N1, push(TF, N0)}).


frequent_build_subseqs(Sequences) ->
    frequent_build_subseqs(Sequences, lists:duplicate(?BITWIDTH, 0)).

frequent_build_subseqs([], Roots) ->
    Roots;
frequent_build_subseqs([Sequence|Sequences], Tmproots) ->
io:format("Another ~p\n", [length(Sequences)]),
clean(Tmproots),
    Subseq = online_build_subseq(Sequence),
    frequent_build_subseqs(Sequences, cache_add(Tmproots, lists:duplicate(?BITWIDTH - 1, 0) ++ [Subseq])).



frequent_build_subword(Sequence) ->
    frequent_build_subword(build_prefix(Sequence), lists:duplicate(?BITWIDTH - 1, 0) ++ [1]).

frequent_build_subword(1, Roots) ->
    Roots;
frequent_build_subword(Parent, Tmproots) ->
    Newroots = add(lists:duplicate(?BITWIDTH - 1, 0) ++ [Parent], Tmproots),
    [{_, {_, Child, _}}] = ets:lookup(nodememory, Parent),
    frequent_build_subword(Child, Newroots).


star_build_subword(Sequence) ->
    star_build_subword(lists:reverse(Sequence), 1, 1).

star_build_subword([], _, Root) ->
    Root;
star_build_subword([Item|Items], Prefix, Tmproot) ->
    Newprefix = store({-1, Prefix, store({Item, Prefix, 1})}),
    Newroot = subword_union(Newprefix, Tmproot),
    star_build_subword(Items, Newprefix, Newroot).


clean_build_subword(Sequence) ->
    [{_, Lastclean}] = ets:lookup(nodememory, node_number),
    clean_build_subword(lists:reverse(Sequence), Lastclean, 1, 1).

clean_build_subword([], _, _, Root) ->
    Root;
clean_build_subword([Item|Items], Lastclean, Prefix, Tmproot) ->
    Newprefix = store({Item, Prefix, 1}),
    Newroot = cacheless_subword_union(Newprefix, Tmproot),
    if
      Newroot - Lastclean > ?CLEANNUMBER ->
	    clean([Newprefix, Newroot]),
            io:format("~p\n", [length(Items)]),
	    clean_build_subword(Items, Newroot, Newprefix, Newroot);
      true ->
	    clean_build_subword(Items, Lastclean, Newprefix, Newroot)
    end.


cacheless_build_subword(Sequence) ->
    cacheless_build_subword(lists:reverse(Sequence), 1, 1).

cacheless_build_subword([], _, Root) ->
    Root;
cacheless_build_subword([Item|Items], Prefix, Tmproot) ->
    Newprefix = store({Item, Prefix, 1}),
    Newroot = cacheless_subword_union(Newprefix, Tmproot),
    cacheless_build_subword(Items, Newprefix, Newroot).


position_build_subword(Sequence) ->
    Bottom = store({0, 1, 1}),
    ets:insert(cache, {{position, Bottom}, 0}),
    position_build_subword(Sequence, 1, Bottom, 1).
    %position_build_subword(lists:reverse(Sequence), 1, Bottom, 1).

position_build_subword([], _, _, Root) ->
    Root;
position_build_subword([Item|Items], Position, Prefix, Tmproot) ->
    Newprefix = store({Item, Prefix, 1}),
    Newroot = subword_union(Newprefix, Tmproot),
    ets:insert(cache, {{position, Newprefix}, Position}),
    position_build_subword(Items, Position + 1, Newprefix, Newroot).



negation(N) when N =< 1 ->
    N bxor 1;
negation(N) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    store({X, negation(N1), negation(N0)}).


union(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    union(P, Q, Pnode, Qnode).

union(P, 0, _, _) ->
    P;
union(0, Q, _, _) ->
    Q;
union(1, 1, _, _) ->
    1;
union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P < Q ->
    Hit = ets:lookup(cache, {union, P, Q}),
    case Hit of
      [{_, Result}] ->
	    Result;
      _ ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = store({X, P1, union(P0, Q, P0node, {Y, Q1, Q0})}),
                    ets:insert(cache, {{union, P, Q}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = store({Y, Q1, union(P, Q0, {X, P1, P0}, Q0node)}),
		    ets:insert(cache, {{union, P, Q}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, union(P1, Q1, P1node, Q1node), union(P0, Q0, P0node, Q0node)}),
		    ets:insert(cache, {{union, P, Q}, Number}),
		    Number
	      end
    end;
union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P > Q ->
    Hit = ets:lookup(cache, {union, Q, P}),
    case Hit of
      [{_, Result}] ->
	    Result;
      _ ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = store({X, P1, union(P0, Q, P0node, {Y, Q1, Q0})}),
                    ets:insert(cache, {{union, Q, P}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = store({Y, Q1, union(P, Q0, {X, P1, P0}, Q0node)}),
		    ets:insert(cache, {{union, Q, P}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, union(P1, Q1, P1node, Q1node), union(P0, Q0, P0node, Q0node)}),
		    ets:insert(cache, {{union, Q, P}, Number}),
		    Number
	      end
    end;
union(P, P, _, _) ->
    P.


intersect(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    intersect(P, Q, Pnode, Qnode).

intersect(P, Q, _, _) when P =:= 0; Q =:= 0 ->
    0;
intersect(1, 1, _, _) ->
    1;
intersect(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P < Q ->
    Hit = ets:lookup(cache, {intersect, P, Q}),
    case Hit of
      [{_, Result}] ->
	    Result;
      _ ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = intersect(P0, Q, P0node, {Y, Q1, Q0}),
                    ets:insert(cache, {{intersect, P, Q}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = intersect(P, Q0, {X, P1, P0}, Q0node),
		    ets:insert(cache, {{intersect, P, Q}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, intersect(P1, Q1, P1node, Q1node), intersect(P0, Q0, P0node, Q0node)}),
		    ets:insert(cache, {{intersect, P, Q}, Number}),
		    Number
	      end
    end;
intersect(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P > Q ->
    Hit = ets:lookup(cache, {intersect, Q, P}),
    case Hit of
      [{_, Result}] ->
	    Result;
      _ ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = intersect(P0, Q, P0node, {Y, Q1, Q0}),
                    ets:insert(cache, {{intersect, Q, P}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = intersect(P, Q0, {X, P1, P0}, Q0node),
		    ets:insert(cache, {{intersect, Q, P}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, intersect(P1, Q1, P1node, Q1node), intersect(P0, Q0, P0node, Q0node)}),
		    ets:insert(cache, {{intersect, Q, P}, Number}),
		    Number
	      end
    end;
intersect(P, P, _, _) ->
    P.


minus(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    minus(P, Q, Pnode, Qnode).

minus(P, 0, _, _) ->
    P;
minus(0, _, _, _) ->
    0;
minus(P, P, _, _) ->
    0;
minus(P, Q, {X, P1, P0}, {Y, Q1, Q0}) ->
    Hit = [],%ets:lookup(cache, {minus, P, Q}),
    case Hit of
      [{_, Result}] ->
	    Result;
      _ ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = store({X, P1, minus(P0, Q, P0node, {Y, Q1, Q0})}),
                    ets:insert(cache, {{minus, P, Q}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = minus(P, Q0, {X, P1, P0}, Q0node),
		    ets:insert(cache, {{minus, P, Q}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, minus(P1, Q1, P1node, Q1node), minus(P0, Q0, P0node, Q0node)}),
		    ets:insert(cache, {{minus, P, Q}, Number}),
		    Number
	      end
    end.


exclusive_or(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    exclusive_or(P, Q, Pnode, Qnode).


exclusive_or(0, 0, _, _) ->
    1;
exclusive_or(0, Q, _, _) ->
    Q;
exclusive_or(P, 0, _, _) ->
    P;
exclusive_or(1, 1, _, _) ->
    0;
exclusive_or(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P < Q ->
    Hit = ets:lookup(cache, {exclusive_or, P, Q}),
    case Hit of
      [{_, Result}] ->
	    Result;
      _ ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = store({X, P1, exclusive_or(P0, Q, P0node, {Y, Q1, Q0})}),
                    ets:insert(cache, {{exclusive_or, P, Q}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = store({Y, Q1, exclusive_or(P, Q0, {X, P1, P0}, Q0node)}),
		    ets:insert(cache, {{exclusive_or, P, Q}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, exclusive_or(P1, Q1, P1node, Q1node), exclusive_or(P0, Q0, P0node, Q0node)}),
		    ets:insert(cache, {{exclusive_or, P, Q}, Number}),
		    Number
	      end
    end;
exclusive_or(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P > Q ->
    Hit = ets:lookup(cache, {exclusive_or, Q, P}),
    case Hit of
      [{_, Result}] ->
	    Result;
      _ ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = store({X, P1, exclusive_or(P0, Q, P0node, {Y, Q1, Q0})}),
                    ets:insert(cache, {{exclusive_or, Q, P}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = store({Y, Q1, exclusive_or(P, Q0, {X, P1, P0}, Q0node)}),
		    ets:insert(cache, {{exclusive_or, Q, P}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, exclusive_or(P1, Q1, P1node, Q1node), exclusive_or(P0, Q0, P0node, Q0node)}),
		    ets:insert(cache, {{exclusive_or, Q, P}, Number}),
		    Number
	      end
    end;
exclusive_or(P, P, _, _) ->
    0.


subword_union(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    subword_union(P, Q, Pnode, Qnode).

subword_union(P, Q, _, _) when Q =< 1 ->
    P;
subword_union(P, Q, _, _) when P =< 1 ->
    Q;
subword_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P < Q ->
    Hit = ets:lookup(cache, {union, P, Q}),
    case Hit of
      [{_, Result}] ->
	    Result;
      _ ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = store({X, P1, subword_union(P0, Q, P0node, {Y, Q1, Q0})}),
                    ets:insert(cache, {{union, P, Q}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = store({Y, Q1, subword_union(P, Q0, {X, P1, P0}, Q0node)}),
		    ets:insert(cache, {{union, P, Q}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, subword_union(P1, Q1, P1node, Q1node), subword_union(P0, Q0, P0node, Q0node)}),
		    ets:insert(cache, {{union, P, Q}, Number}),
		    Number
	      end
    end;
subword_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P > Q ->
    Hit = ets:lookup(cache, {union, Q, P}),
    case Hit of
      [{_, Result}] ->
	    Result;
      _ ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = store({X, P1, subword_union(P0, Q, P0node, {Y, Q1, Q0})}),
                    ets:insert(cache, {{union, Q, P}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = store({Y, Q1, subword_union(P, Q0, {X, P1, P0}, Q0node)}),
		    ets:insert(cache, {{union, Q, P}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, subword_union(P1, Q1, P1node, Q1node), subword_union(P0, Q0, P0node, Q0node)}),
		    ets:insert(cache, {{union, Q, P}, Number}),
		    Number
	      end
    end;
subword_union(P, P, _, _) ->
    P.




add(Abitlist, Bbitlist) ->
    add(lists:reverse(Abitlist), lists:reverse(Bbitlist), 0, []).

add([], [], _, Resultlist) ->
    Resultlist;
add([0|Abits], [0|Bbits], 0, Resultlist) ->
    add(Abits, Bbits, 0, [0|Resultlist]);
add([Abit|Abits], [Bbit|Bbits], C, Resultlist) ->
    [{_, Anode}] = ets:lookup(nodememory, Abit),
    [{_, Bnode}] = ets:lookup(nodememory, Bbit),
    [{_, Cnode}] = ets:lookup(nodememory, C),
    {N, Carry} = add(Abit, Bbit, C, Anode, Bnode, Cnode),
    add(Abits, Bbits, Carry, [N|Resultlist]).

add(A, A, A, _, _, _) ->
    {A, A};
add(A, A, C, _, _, _) ->
    {C, A};
add(A, B, B, _, _, _) ->
    {A, B};
add(C, B, C, _, _, _) ->
    {B, C};
add(A, B, C, _, _, _) when A =< 1, B =< 1, C =< 1 ->
    {(A+B+C) band 1, (A+B+C) bsr 1};
add(A, B, C, {X, A1, A0}, {Y, B1, B0}, {Z, C1, C0}) ->
    if
      X < Y ->
	    if
              X < Z ->
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    {N, Carry} = add(A0, B, C, A0node, {Y, B1, B0}, {Z, C1, C0}),
		    {store({X, A1, N}), Carry};
	      Z < X ->
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {N, Carry} = add(A, B, C0, {X, A1, A0}, {Y, B1, B0}, C0node),
		    {store({Z, C1, N}), Carry};
	      true ->
		    [{_, A1node}] = ets:lookup(nodememory, A1),
		    [{_, C1node}] = ets:lookup(nodememory, C1),
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {M, Mcarry} = add(A1, 0, C1, A1node, {false, 0, 0}, C1node),
		    {N, Ncarry} = add(A0, B, C0, A0node, {Y, B1, B0}, C0node),
		    {store({X, M, N}), store({X, Mcarry, Ncarry})}
            end;
      Y < X ->
	    if
              Y < Z ->
		    [{_, B0node}] = ets:lookup(nodememory, B0),
		    {N, Carry} = add(A, B0, C, {X, A1, A0}, B0node, {Z, C1, C0}),
		    {store({Y, B1, N}), Carry};
	      Z < Y ->
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {N, Carry} = add(A, B, C0, {X, A1, A0}, {Y, B1, B0}, C0node),
		    {store({Z, C1, N}), Carry};
	      true ->
		    [{_, B1node}] = ets:lookup(nodememory, B1),
		    [{_, C1node}] = ets:lookup(nodememory, C1),
		    [{_, B0node}] = ets:lookup(nodememory, B0),
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {M, Mcarry} = add(0, B1, C1, {false, 0, 0}, B1node, C1node),
		    {N, Ncarry} = add(A, B0, C0, {X, A1, A0}, B0node, C0node),
		    {store({Y, M, N}), store({Y, Mcarry, Ncarry})}
            end;
      true ->
            if
	      X < Z ->
		    [{_, A1node}] = ets:lookup(nodememory, A1),
		    [{_, B1node}] = ets:lookup(nodememory, B1),
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    [{_, B0node}] = ets:lookup(nodememory, B0),
		    {M, Mcarry} = add(A1, B1, 0, A1node, B1node, {false, 0, 0}),
		    {N, Ncarry} = add(A0, B0, C, A0node, B0node, {Z, C1, C0}),
		    {store({X, M, N}), store({X, Mcarry, Ncarry})};
	      Z < X ->
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {N, Carry} = add(A, B, C0, {X, A1, A0}, {Y, B1, B0}, C0node),
		    {store({Z, C1, N}), Carry};
	      true ->
		    [{_, A1node}] = ets:lookup(nodememory, A1),
		    [{_, B1node}] = ets:lookup(nodememory, B1),
                    [{_, C1node}] = ets:lookup(nodememory, C1),
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    [{_, B0node}] = ets:lookup(nodememory, B0),
                    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {M, Mcarry} = add(A1, B1, C1, A1node, B1node, C1node),
		    {N, Ncarry} = add(A0, B0, C0, A0node, B0node, C0node),
		    {store({X, M, N}), store({X, Mcarry, Ncarry})}
            end
    end.


subtract(Abitlist, Bbitlist) ->
    subtract(lists:reverse(Abitlist), lists:reverse(Bbitlist), 0, []).

subtract([], [], _, Resultlist) ->
    Resultlist;
subtract([0|Abits], [0|Bbits], Carry, Resultlist) ->
    subtract(Abits, Bbits, Carry, [Carry|Resultlist]);
subtract([Abit|Abits], [Bbit|Bbits], C, Resultlist) ->
    [{_, Anode}] = ets:lookup(nodememory, Abit),
    [{_, Bnode}] = ets:lookup(nodememory, Bbit),
    [{_, Cnode}] = ets:lookup(nodememory, C),
    {N, Carry} = subtract(Abit, Bbit, C, Anode, Bnode, Cnode),
    subtract(Abits, Bbits, Carry, [N|Resultlist]).

subtract(A, B, C, _, _, _) when A =:= B, C =:= 0; A =:= C, B =:= 0 ->
    {0, 0};
subtract(A, B, C, _, _, _) when A =< 1, B =< 1, C =< 1 ->
    {(A+B+C) band 1, ((A-B-C) band 2) bsr 1};
subtract(A, B, C, {X, A1, A0}, {Y, B1, B0}, {Z, C1, C0}) ->
    if
      X < Y ->
	    if
              X < Z ->
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    {N, Carry} = subtract(A0, B, C, A0node, {Y, B1, B0}, {Z, C1, C0}),
		    {store({X, A1, N}), Carry};
	      Z < X ->
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {N, Carry} = subtract(A, B, C0, {X, A1, A0}, {Y, B1, B0}, C0node),
		    {store({Z, C1, N}), store({Z, C1, Carry})};
	      true ->
		    [{_, A1node}] = ets:lookup(nodememory, A1),
		    [{_, C1node}] = ets:lookup(nodememory, C1),
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {M, Mcarry} = subtract(A1, 0, C1, A1node, {false, 0, 0}, C1node),
		    {N, Ncarry} = subtract(A0, B, C0, A0node, {Y, B1, B0}, C0node),
		    {store({X, M, N}), store({X, Mcarry, Ncarry})}
            end;
      Y < X ->
	    if
              Y < Z ->
		    [{_, B0node}] = ets:lookup(nodememory, B0),
		    {N, Carry} = subtract(A, B0, C, {X, A1, A0}, B0node, {Z, C1, C0}),
		    {store({Y, B1, N}), store({Y, B1, Carry})};
	      Z < Y ->
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {N, Carry} = subtract(A, B, C0, {X, A1, A0}, {Y, B1, B0}, C0node),
		    {store({Z, C1, N}), store({Z, C1, Carry})};
	      true ->
		    [{_, B1node}] = ets:lookup(nodememory, B1),
		    [{_, C1node}] = ets:lookup(nodememory, C1),
		    [{_, B0node}] = ets:lookup(nodememory, B0),
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {M, Mcarry} = subtract(0, B1, C1, {false, 0, 0}, B1node, C1node),
		    {N, Ncarry} = subtract(A, B0, C0, {X, A1, A0}, B0node, C0node),
		    {store({Y, M, N}), store({Y, Mcarry, Ncarry})}
            end;
      true ->
            if
	      X < Z ->
		    [{_, A1node}] = ets:lookup(nodememory, A1),
		    [{_, B1node}] = ets:lookup(nodememory, B1),
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    [{_, B0node}] = ets:lookup(nodememory, B0),
		    {M, Mcarry} = subtract(A1, B1, 0, A1node, B1node, {false, 0, 0}),
		    {N, Ncarry} = subtract(A0, B0, C, A0node, B0node, {Z, C1, C0}),
		    {store({X, M, N}), store({X, Mcarry, Ncarry})};
	      Z < X ->
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {N, Carry} = subtract(A, B, C0, {X, A1, A0}, {Y, B1, B0}, C0node),
		    {store({Z, C1, N}), store({Z, C1, Carry})};
	      true ->
		    [{_, A1node}] = ets:lookup(nodememory, A1),
		    [{_, B1node}] = ets:lookup(nodememory, B1),
                    [{_, C1node}] = ets:lookup(nodememory, C1),
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    [{_, B0node}] = ets:lookup(nodememory, B0),
                    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {M, Mcarry} = subtract(A1, B1, C1, A1node, B1node, C1node),
		    {N, Ncarry} = subtract(A0, B0, C0, A0node, B0node, C0node),
		    {store({X, M, N}), store({X, Mcarry, Ncarry})}
            end
    end.


all_node(R) ->
  ets:new(tmpcache, [private, named_table]),
  L = all_node(R, []),
  ets:delete(tmpcache),
  L.

all_node(0, L) ->
  L;
all_node(1, L) ->
  L;
all_node(N, L) ->
  Object = ets:lookup(tmpcache, N),
  case Object of
    [] ->
      [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
      L0 = all_node(N0, L),
      L1 = all_node(N1, L0),
      [N|L1];
    _ ->
      L
  end.


multi_union_subword(R) when not is_list(R) ->
  multi_union_subword([R]);
multi_union_subword(L) ->
  ets:new(tmpcache, [private, named_table]),
  Ns = seq:set(lists:sort(lists:map(fun(N) -> [{_, {X, N1, _}}] = ets:lookup(nodememory, N), store({X, N1, 1}) end, L))),
  R = multi_union_subword(Ns, lists:map(fun(N) -> [{_, Node}] = ets:lookup(nodememory, N), Node end, Ns)),
  ets:delete(tmpcache),
  R.

multi_union_subword([], _) ->
  1;
multi_union_subword([N], _) ->
  N;
multi_union_subword([P, Q], [PNode, QNode]) ->
  subword_union(P, Q, PNode, QNode);
multi_union_subword(Ns, Nodes) ->
  Object = [],%ets:lookup(tmpcache, Ns),
  case Object of
    [] ->
      {A, Ms, Modes, N1s, N0s} = multi_union_subword_loop(Ns, Nodes, 65536),
      {M0s, Mode0s} = node_merge(Ms, Modes, seq:set(lists:sort(N0s))),
      M1s = seq:set(lists:sort(N1s)),
      R = store({A, multi_union_subword(M1s, lists:map(fun(M1) -> [{_, Mode1}] = ets:lookup(nodememory, M1), Mode1 end, M1s)), multi_union_subword(M0s, Mode0s)}),
      %ets:insert(tmpcache, {Ns, R}),
      R;
    [{_, R}] ->
      R
  end.

multi_union_subword_loop([], _, A) ->
    {A, [], [], [], []};
multi_union_subword_loop([N|Ns], [{X, N1, N0}|Nodes], Z) ->
    B = lists:min([Z, X]),
    {A, Ms, Modes, N1s, N0s} = multi_union_subword_loop(Ns, Nodes, B),
    case A of
      X ->
        case N1 of
          1 ->
            case N0 of
              1 -> {A, Ms, Modes, N1s, N0s};
              _ -> {A, Ms, Modes, N1s, [N0|N0s]}
            end;
          _ ->
            case N0 of
              1 -> {A, Ms, Modes, [N1|N1s], N0s};
              _ -> {A, Ms, Modes, [N1|N1s], [N0|N0s]}
            end
        end;
      _ ->
        {A, [N|Ms], [{X, N1, N0}|Modes], N1s, N0s}
    end.

node_merge(Ms, Modes, []) ->
  {Ms, Modes};
node_merge([], _, N0s) ->
  {N0s, lists:map(fun(N0) -> [{_, Node}] = ets:lookup(nodememory, N0), Node end, N0s)};
node_merge([M|Ms], [Mode|Modes], [N0|N0s]) ->
  if
    M < N0 ->
      {M0s, Mode0s} = node_merge(Ms, Modes, [N0|N0s]),
      {[M|M0s], [Mode|Mode0s]};
    M > N0 ->
      {M0s, Mode0s} = node_merge([M|Ms], [Mode|Modes], N0s),
      [{_, Node0}] = ets:lookup(nodememory, N0),
      {[N0|M0s], [Node0|Mode0s]};
    true ->
      {M0s, Mode0s} = node_merge(Ms, Modes, N0s),
      {[M|M0s], [Mode|Mode0s]}
  end.


all_setoperation([Result], _) ->
    Result;
all_setoperation([P|[Q|Remainder]], Operation) ->
    all_setoperation([Operation(P, Q)|Remainder], Operation).


product(0, _) ->
  0;
product(1, B) ->
  B;
product(A, B) ->
  Result = ets:lookup(cache, {product, A, B}),
  case Result of
    [] ->
      [{_, {X, A1, A0}}] = ets:lookup(nodememory, A),
      P = union(store({X, product(A1, B), 0}), product(A0, B)),
      ets:insert(cache, {{product, A, B}, P}),
      P;
    [{_, C}] ->
      C
  end.


reverse(0) ->
  0;
reverse(1) ->
  1;
reverse(P) ->
  Result = ets:lookup(cache, {reverse, P}),
  case Result of
    [] ->
      [{_, {X, P1, P0}}] = ets:lookup(nodememory, P),
      R = union(product(reverse(P1), store({X, 1, 0})), reverse(P0)),
      ets:insert(cache, {{reverse, R}, R}),
      R;
    [{_, R}] ->
      R
  end.


in(P, Q) ->
    R = union(P, Q),
    case R of
      Q ->
	    true;
      _ ->
	    false
    end.

sub(Substring, String) ->
    Contain = in(build_subword(Substring), build_subword(String)),
    if
      Contain ->
	    true;
      true ->
	    false
    end.


contain_subseq(N, Sequence) when is_list(Sequence) ->
  Root = build(Sequence),
  contain_subseq(N, Root);
contain_subseq(N, 1) ->
  N;
contain_subseq(N, _) when N =< 1 ->
  0;
contain_subseq(N, Parent) ->
  Result = ets:lookup(cache, {contain_subseq, N, Parent}),
  case Result of
    [] ->
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      [{_, {C, Child, _}}] = ets:lookup(nodememory, Parent),
      if
        X =:= C ->
          Contain = store({X, contain_subseq(N1, Child), contain_subseq(N0, Parent)});
        true ->
          Contain = store({X, contain_subseq(N1, Parent), contain_subseq(N0, Parent)})
      end,
      ets:insert(cache, {{contain_subseq, N, Parent}, Contain}),
      Contain;
    [{_, Contain}] ->
      Contain
  end.


contain_substr(N, Sequence) ->
  Root = build(Sequence),
  contain_substr(N, Root, Root).
contain_substr(N, 1, _) ->
  N;
contain_substr(N, _, _) when N =< 1 ->
  0;
contain_substr(N, Root, Root) ->
  Result = ets:lookup(cache, {contain_substr, N, Root, false}),
  case Result of
    [] ->
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      [{_, {C, Child, _}}] = ets:lookup(nodememory, Root),
      if
        X =:= C ->
          Contain = store({X, union(contain_substr(N1, Child, Root), contain_substr(N1, Root, Root)), contain_substr(N0, Root, Root)});
        true ->
          Contain = store({X, contain_substr(N1, Root, Root), contain_substr(N0, Root, Root)})
      end,
      ets:insert(cache, {{contain_substr, N, Root, false}, Contain}),
      Contain;
    [{_, Contain}] ->
      Contain
  end;
contain_substr(N, Parent, Root) ->
  Result = ets:lookup(cache, {contain_substr, N, Parent, true}),
  case Result of
    [] ->
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      [{_, {C, Child, _}}] = ets:lookup(nodememory, Parent),
      if
        X =:= C ->
          Contain = store({X, contain_substr(N1, Child, Root), 0});
        true ->
          Contain = contain_substr(N0, Parent, Root)
      end,
      ets:insert(cache, {{contain_substr, N, Parent, true}, Contain}),
      Contain;
    [{_, Contain}] ->
      Contain
  end.


search(0, _) ->
    false;
search(1, []) ->
    true;
search(1, _) ->
    false;
search(N, []) ->
    [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
    search(N0, []);
search(N, [Item|Items]) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    if
      Item < X ->
	    false;
      Item > X ->
	    search(N0, [Item|Items]);
      true ->
	    search(N1, Items)
    end.


print(Root) ->
    print(Root, []).

print(0, _) ->
    ok;
print(1, Rsequence) ->
    io:format("~s\n", [lists:reverse(Rsequence)]);
print(N, Rprefix) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    if
      is_atom(X) -> 
        io:format("~s\n", [lists:reverse(Rprefix)]);
      X =:= -1 ->
        print(N1, [63|Rprefix]),
        print(N0, Rprefix);
      true ->
        print(N1, [X|Rprefix]),
        print(N0, Rprefix)
    end.


printfile(Root, Filename) ->
  {B, O} = file:open(Filename, [write]),
  case B of
    ok ->
      printfile(Root, [], O);
    error ->
      0
  end.

printfile(0, _, _) ->
    ok;
printfile(1, Rsequence, O) ->
    file:write(O, lists:reverse([10,13] ++ Rsequence));
printfile(N, Rprefix, O) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    if
      is_atom(X) -> 
        file:write(O, lists:reverse([10,13] ++ Rprefix));
        %io:format("~s\n", [lists:reverse(Rprefix)]);
      X =:= -1 ->
        printfile(N1, [63|Rprefix], O),
        printfile(N0, Rprefix, O);
      true ->
        printfile(N1, [X|Rprefix], O),
        printfile(N0, Rprefix, O)
    end.


seqbdd2file(Root, Filename) ->
    {_, File} = file:open(Filename, [write]),
    seqbdd2file(Root, File, []),
    file:close(File).

seqbdd2file(0, _, _) ->
    ok;
seqbdd2file(1, File, Rsequence) ->
    io:fwrite(File, "~s\n", [lists:reverse(Rsequence)]);
seqbdd2file(N, File, Rprefix) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    seqbdd2file(N1, File, [X|Rprefix]),
    seqbdd2file(N0, File, Rprefix).


count({N}) when N =< 1 ->
  Object = ets:lookup(counter, N),
  case Object of
    [] ->
      ets:insert(counter, {N, true}),
      1;
    _ ->
      0
  end;
count({N}) ->
    Object = ets:lookup(counter, N),
    case Object of
      [] ->
            ets:insert(counter, {N, true}),
	    [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
	    count({N1}) + count({N0}) + 1;
      _ ->
	    0
    end;
count(Root) ->
    ets:new(counter, [private, named_table]),
    Number = count({Root}),
    ets:delete(counter),
    Number.


multi_count(R) when not is_list(R) ->
  count(R);
multi_count(L) ->
  ets:new(counter, [private, named_table]),
  multi_count(L, 0).

multi_count([], Num) ->
  ets:delete(counter),
  Num;
multi_count([R|Rs], Num) ->
  multi_count(Rs, Num + count({R})).


tree_count(0) ->
  1;
tree_count(1) ->
  1;
tree_count(N) ->
  Object = ets:lookup(cache, {tree_count, N}),
  case Object of
    [] ->
      [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
      Number = 1 + tree_count(N1) + tree_count(N0),
      ets:insert(cache, {{tree_count, N}, Number}),
      Number;
    [{_, Number}] ->
      Number
  end.


death_count(N) ->
  Object = ets:lookup(nodememory, N),
  case Object of
    [] ->
      0;
    [{_, {X, N1, N0}}] ->
      ets:delete(nodememory, N),
      ets:delete(uniquetable, {X, N1, N0}),
      1 + death_count(N1) + death_count(N0)
  end.


path(0) ->
    ets:insert(cache, {{path, 0}, 0}),
    0;
path(1) ->
    ets:insert(cache, {{path, 1}, 1}),
    1;
path(N) ->
    Result = ets:lookup(cache, {path, N}),
    case Result of
      [] ->
	    [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
	    Number = path(N1) + path(N0),
	    ets:insert(cache, {{path, N}, Number}),
	    Number;
      [{_, Number}] ->
	    Number
    end.


depth(N) when N =< 1 ->
    ets:insert(cache, {{depth, N}, 0}),
    0;
depth(N) ->
    Result = ets:lookup(cache, {depth, N}),
    case Result of
      [] ->
            [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
	    Depth = lists:max([depth(N1) + 1, depth(N0)]),
	    ets:insert(cache, {{depth, N}, Depth}),
	    Depth;
      [{_, Depth}] ->
	    Depth
    end.


shallowness(N) when N =:= 0 ->
    ets:insert(cache, {{shallowness, N}, 1 bsl ?BITWIDTH}),
    1 bsl ?BITWIDTH;
shallowness(N) when N =:= 1 ->
    ets:insert(cache, {{shallowness, N}, 0}),
    0;
shallowness(N) ->
    Result = ets:lookup(cache, {shallowness, N}),
    case Result of
      [] ->
            [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
	    Distance = lists:min([shallowness(N1) + 1, shallowness(N0)]),
	    ets:insert(cache, {{shallowness, N}, Distance}),
	    Distance;
      [{_, Distance}] ->
	    Distance
    end.


number(N, _) when N =< 1 ->
  0;
number(N, Delimiters) ->
  Result = ets:lookup(cache, {number, N}),
  case Result of
    [] ->
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      Isdelimiter = lists:member(X, Delimiters),
      case Isdelimiter of
        false ->
          Plus = 0;
        true ->
          Plus = 1
      end,
      Number = number(N1, Delimiters) + number(N0, Delimiters) + Plus,
      ets:insert(cache, {{number, N}, Number}),
      Number;
    [{_, Number}] ->
      Number
  end.


much(N, Min, Delimiters) ->
  number(N, Delimiters),
  much(N, Min).
much(N, _) when N =< 1 ->
  0;
much(N, Min) ->
  Result = ets:lookup(cache, {much, N, Min}),
  case Result of
    [] ->
        [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
        [{_, Number}] = ets:lookup(cache, {number, N}),
        if
          Number < Min ->
            0;
          true ->
            union(store({X, much(N1, Min), much(N0, Min)}), 1)
        end;
    [{_, M}] ->
      M
    end.


longest(N) ->
    depth(N),
    longest(N, []).
longest(N, Rsequence) when N =< 1 ->
    [lists:reverse(Rsequence)];
longest(N, Rsequence) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    [{_, Length0}] = ets:lookup(cache, {depth, N0}),
    [{_, Length1}] = ets:lookup(cache, {depth, N1}),
    if
      Length0 > Length1 + 1 ->
        longest(N0, Rsequence);
      Length0 < Length1 + 1 ->
        longest(N1, [X|Rsequence]);
      true ->
        longest(N1, [X|Rsequence]) ++ longest(N0, Rsequence)
    end.


shortest(N) ->
    shallowness(N),
    shortest(N, []).
shortest(N, Rsequence) when N =< 1 ->
    lists:reverse(Rsequence);
shortest(N, Rsequence) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    [{_, Length0}] = ets:lookup(cache, {shallowness, N0}),
    [{_, Length1}] = ets:lookup(cache, {shallowness, N1}),
    if
      Length0 > Length1 + 1 ->
        shortest(N1, Rsequence);
      Length0 < Length1 + 1 ->
        shortest(N0, Rsequence);
      true ->
        shortest(N1, [X|Rsequence]) ++ shortest(N0, Rsequence)
    end.


character(N) ->
  character(N, 0).
character(0, _) ->
  0;
character(1, Length) ->
  Length;
character(N, Length) ->
  Result = ets:lookup(cache, {character, N}),
  case Result of
    [] ->
      [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
      C = character(N1, 1) + character(N0, 0),
      ets:insert(cache, {{character, N}, C}),
      character(N1, Length + 1) + character(N0, Length);
    [{_, C}] ->
      Length * path(N) + C
  end.


decompress(Root) ->
    decompress(Root, []).

decompress(0, _) ->
    [];
decompress(1, Rsequence) ->
    [lists:reverse(Rsequence)];
decompress(N, Rsequence) ->
    [{_, {Item, N1, N0}}] = ets:lookup(nodememory, N),
    lists:append(decompress(N1, [Item|Rsequence]), decompress(N0, Rsequence)).


random(Root) ->
    Pathnumber = path(Root),
    Number = random:uniform(Pathnumber),
    random(Root, Number, []).

random(0, _, _) ->
    [];
random(1, _, Rsequence) ->
    lists:reverse(Rsequence);
random(N, Number, Rsequence) ->
    [{_, {Item, N1, N0}}] = ets:lookup(nodememory, N),
    [{_, N1path}] = ets:lookup(cache, {path, N1}),
    if
      Number =< N1path ->
	    random(N1, Number, [Item|Rsequence]);
      true ->
	    random(N0, Number - N1path, Rsequence)
    end.
    


shorter(0, _) ->
  0;
shorter(1, _) ->
  1;
shorter(N, 0) ->
  Result = ets:lookup(cache, {shorter, N, 0}),
  case Result of
    [] -> 
      [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
      R = shorter(N0, 0),
      ets:insert(cache, {{shorter, N, 0}, R}),
      R;
    [{_, R}] ->
      R
  end;
shorter(N, Threshold) ->
  Result = ets:lookup(cache, {shorter, N, Threshold}),
  case Result of
    [] ->
      [{_, {Item, N1, N0}}] = ets:lookup(nodememory, N),
      R = store({Item, shorter(N1, Threshold - 1), shorter(N0, Threshold)}),
      ets:insert(cache, {{shorter, N, Threshold}, R}),
      R;
    [{_, R}] ->
      R
  end.


longer(N, 0) ->
  N;
longer(0, _) ->
  0;
longer(1, 0) ->
  1;
longer(1, _) ->
  0;
longer(N, Threshold) ->
  Result = ets:lookup(cache, {longer, N, Threshold}),
  case Result of
    [] -> 
      [{_, {Item, N1, N0}}] = ets:lookup(nodememory, N),
      R = store({Item, longer(N1, Threshold - 1), longer(N0, Threshold)}),
      ets:insert(cache, {{longer, N, Threshold}, R}),
      R;
    [{_, R}] ->
      R
  end.


just(0, _) ->
  0;
just(1, 0) ->
  1;
just(1, _) ->
  0;
just(N, 0) ->
  Result = ets:lookup(cache, {just, N, 0}),
  case Result of
    [] -> 
      [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
      R = just(N0, 0),
      ets:insert(cache, {{just, N, 0}, R}),
      R;
    [{_, R}] ->
      R
  end;
just(N, Threshold) ->
  Result = ets:lookup(cache, {just, N, Threshold}),
  case Result of
    [] -> 
      [{_, {Item, N1, N0}}] = ets:lookup(nodememory, N),
      R = store({Item, just(N1, Threshold - 1), just(N0, Threshold)}),
      ets:insert(cache, {{just, N, Threshold}, R}),
      R;
    [{_, R}] ->
      R
  end.


%longer(Root, Threshold) ->
%    longer(Root, Threshold, 0, []).
%
%longer(0, _, _, _) ->
%    [];
%longer(1, Threshold, Length, _) when Length < Threshold ->
%    [];
%longer(1, _, _, Rsequence) ->
%    [lists:reverse(Rsequence)];
%longer(N, Threshold, Length, Rsequence) ->
%    [{_, {Item, N1, N0}}] = ets:lookup(nodememory, N),
%    lists:append(longer(N1, Threshold, Length + 1, [Item|Rsequence]), longer(N0, Threshold, Length, Rsequence)).



position(Root, Sequence) when is_list(Sequence) ->
    N = search_node(Root, lists:reverse(Sequence)),
    lists:sort(position(N, 0));
position(N, _) when N =<1 ->
    [];
position(N, Length) ->
    Result = ets:lookup(cache, {position, N}),
    case Result of
      [] ->
	    [{_, {Item, N1, N0}}] = ets:lookup(nodememory, N),
            if
              Item == 0 ->
		    [Length|position(N0, Length)];
	      true ->
		    lists:append(position(N1, Length + 1), position(N0, Length))
            end;
      [{_, Position}] ->
	    [Position + Length]
    end.
    


frequency([Sign|Roots], Sequence) ->
    Found = search(Sign, Sequence),
    case Found of
      true ->
	    frequency(Roots, Sequence, 0) - (1 bsl (?BITWIDTH - 1));
      false ->
	    frequency(Roots, Sequence, 0)
    end.

frequency([], _, Number) ->
    Number;
frequency([Bit|Bits], Sequence, Count) ->
    Found = search(Bit, Sequence),
    case Found of
      true ->
	    frequency(Bits, Sequence, (Count bsl 1) bor 1);
      false ->
	    frequency(Bits, Sequence, Count bsl 1)
    end.


more([Sign|Roots], Min_support) ->
    Result = more(Roots, Min_support, ?BITWIDTH - 2, 0, -1),
    minus(Result, Sign).

more([], _, _, Pass, -1) ->
    Pass;
more([], _, _, Pass, Candidate) ->
    union(Pass, Candidate);
more([Bit|Bits], Min_support, Digit, Pass, -1) ->
    Flag = (Min_support bsr Digit) band 1,
    case Flag of
      0 ->
	    more(Bits, Min_support, Digit - 1, union(Bit, Pass), -1);
      1 ->
	    more(Bits, Min_support, Digit - 1, Pass, Bit)
    end;
more([Bit|Bits], Min_support, Digit, Pass, Candidate) ->
    Flag = (Min_support bsr Digit) band 1,
    case Flag of
      0 ->
	    Newpass = union(Pass, intersect(Bit, Candidate)),
	    more(Bits, Min_support, Digit - 1, Newpass, Candidate);
      1 ->
	    Newcandidate = intersect(Bit, Candidate),
	    more(Bits, Min_support, Digit - 1, Pass, Newcandidate)
    end.


less([Sign|Roots], Max_support) ->
    less(Roots, Max_support, ?BITWIDTH - 2, 0, Sign).

less([], _, _, Pass, Candidate) ->
    union(Pass, Candidate);
less([Bit|Bits], Max_support, Digit, Pass, Candidate) ->
    Flag = (Max_support bsr Digit) band 1,
    case Flag of
      0 ->
	    Newcandidate = intersect(Bit, Candidate),
	    less(Bits, Max_support, Digit - 1, Pass, Newcandidate);
      1 ->
	    Newpass = union(Pass, intersect(Bit, Candidate)),
	    less(Bits, Max_support, Digit - 1, Newpass, Candidate)
    end.


equal([Sign|Roots], Number) ->
    if
      Number >= 0 ->
            minus(equal(Roots, Number, ?BITWIDTH - 2, -1), Sign);
      true ->
	    equal(Roots, Number, ?BITWIDTH - 2, Sign)
    end.

equal([], _, _, Pass) ->
    Pass;
equal([Bit|Bits], Number, Digit, -1) ->
    Flag = (Number bsr Digit) band 1,
    case Flag of
      0 ->
	    equal(Bits, Number, Digit - 1, -1);
      1 ->
	    equal(Bits, Number, Digit - 1, Bit)
    end;
equal([Bit|Bits], Number, Digit, Candidate) ->
    Flag = (Number bsr Digit) band 1,
    case Flag of
      0 ->
	    Newcandidate = minus(Candidate, Bit),
	    equal(Bits, Number, Digit - 1, Newcandidate);
      1 ->
	    Newcandidate = intersect(Candidate, Bit),
	    equal(Bits, Number, Digit - 1, Newcandidate)
    end.


miss_search(Root, Sequence, Limit) ->
    miss_search(Root, Sequence, Limit, []).

miss_search(_, _, Limit, _) when Limit < 0 ->
    [];
miss_search(0, _, _, _) ->
    [];
miss_search(1, [], _, Foundrsequence) ->
    [lists:reverse(Foundrsequence)];
miss_search(1, _, _, _) ->
    [];
miss_search(N, [Item|Items], Limit, Tmprsequence) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    if
      X =:= -1 ->
	    miss_search(N0, [Item|Items], Limit, Tmprsequence) ++ miss_search(N1, Items, Limit - 1, [35|Tmprsequence]);
      X < Item ->
	    miss_search(N0, [Item|Items], Limit, Tmprsequence);
      X > Item ->
	    [];
      true ->
	    miss_search(N1, Items, Limit, [Item|Tmprsequence])
    end;
miss_search(N, [], Limit, Rsequence) ->
    [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
    miss_search(N0, [], Limit, Rsequence).


search_node(0, _) ->
    0;
search_node(N, []) ->
    N;
search_node(N, [Item|Items]) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    if
      Item < X ->
	    0;
      Item > X ->
	    search_node(N0, [Item|Items]);
      true ->
	    search_node(N1, Items)
    end.


headappend([], _) ->
    [];
headappend(["#"|Sequences], Item) ->
    [[Item]|headappend(Sequences, Item)];
headappend([Sequence|Sequences], Item) ->
    [[Item|Sequence]|headappend(Sequences, Item)].


suffix(Root, Sequence) ->
    ets:new(suffix, [private, named_table]),
    N = search_node(Root, Sequence),
    List = suffix(N),
    ets:delete(suffix),
    List.

suffix(0)  ->
    [];
suffix(1) ->
    ["#"];
suffix(N) ->
    Object = ets:lookup(suffix, N),
    case Object of
      [] ->
	    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
	    List = headappend(suffix(N1), X) ++ suffix(N0),
            ets:insert(suffix, {N, List}),
            List;
      [{_, List}] ->
	    List
    end.


psdd(0) ->
  0;
psdd(R) ->
  recpsdd(R).

recpsdd(0) ->
  1;
recpsdd(1) ->
  1;
recpsdd(N) -> 
    Object = ets:lookup(cache, {psdd, N}),
    case Object of
      [] ->
        [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
        P0 = recpsdd(N0),
        P1 = recpsdd(N1),
        P = store({X, P1, P0}),
        ets:insert(cache, {{psdd, N}, P}),
        ets:insert(cache, {{psdd, P}, P}),
        P;
      [{_, P}] ->
        P
    end.


ssdd(0) ->
    0;
ssdd(R) ->
    ets:new(tmpcache, [private, named_table]),
    S = ssdd(R, 1),
    ets:delete(tmpcache),
    S.

ssdd(0, S) ->
    S;
ssdd(1, S) ->
    S;
ssdd(N, S) ->
    Object = ets:lookup(tmpcache, {visited, N}),
    case Object of
      [] ->
        ets:insert(tmpcache, {{visited, N}, true}),
        [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
        S0 = ssdd(N0, S),
        S1 = ssdd(N1, S0),
        N2 = store({X, N1, 0}),
        Object2 = ets:lookup(tmpcache, {unioned, N2}),
        case Object2 of
          [] ->
            ets:insert(tmpcache, {{unioned, N2}, true}),
            union(S1, N2);
          [{_, _}] ->
            S1
        end;
      [{_, _}] ->
        S
    end.


fsdd_dfa(L) when is_list(L) ->
  multi_union_subword(all_node(multi_build_once_prefix(L)));
fsdd_dfa(0) ->
    0;
fsdd_dfa(R) ->
    ets:new(tmpcache, [private, named_table]),
    {_, F} = fsdd_dfa(R, 1),
    ets:delete(tmpcache),
    F.

fsdd_dfa(0, F) ->
    {1, F};
fsdd_dfa(1, F) ->
    {1, F};
fsdd_dfa(N, F) ->
    Object = ets:lookup(tmpcache, {visited, N}),
    case Object of
      [] ->
        [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
        {P0, F0} = fsdd_dfa(N0, F),
        {P1, F1} = fsdd_dfa(N1, F0),
        P = store({X, P1, P0}),
        ets:insert(tmpcache, {{visited, N}, P}),
        ets:insert(tmpcache, {{visited, P}, P}),
        N2 = store({X, P1, 0}),
        Object2 = ets:lookup(tmpcache, {unioned, N2}),
        case Object2 of
          [] ->
            ets:insert(tmpcache, {{unioned, N2}, true}),
            {P, union(F1, N2)};
          [{_, _}] ->
            {P, F1}
        end;
      [{_, P}] ->
        {P, F}
    end.


fsdd(N) ->
  ssdd(psdd(N)).



%fsdd_rec(1) ->
%  1;
%fsdd_rec(N) ->
%  Object = ets:lookup(cache, {fsdd, N}),
%  case Object of
%    [] ->
%      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
%      P0 = fsdd_rec(N0),
%      P1 = fsdd_rec(N1),
%      R = union(union(store({X, N1, 1}), P0), P1),
%      ets:insert(cache, {{fsdd, N}, R}),
%      R;
%    [{_, R}] ->
%      R
%  end.


fsdd_rec0(0) ->
  0;
fsdd_rec0(1) ->
  1;
fsdd_rec0(N) ->
  Object = ets:lookup(cache, {fsdd, N}),
  case Object of
    [] ->
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      P0 = fsdd_rec0(N0),
      P1 = fsdd_rec0(N1),
      R = union(union(store({X, N1, 0}), P0), P1),
      ets:insert(cache, {{fsdd, N}, R}),
      R;
    _ ->
      0
  end.


fsdd_once(N) ->
  multi_union_subword(all_node(N)).






cacheless_union(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    cacheless_union(P, Q, Pnode, Qnode).

cacheless_union(P, 0, _, _) ->
    P;
cacheless_union(0, Q, _, _) ->
    Q;
cacheless_union(1, 1, _, _) ->
    1;
cacheless_union(P, P, _, _) ->
    P;
cacheless_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    store({X, P1, cacheless_union(P0, Q, P0node, {Y, Q1, Q0})});
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    store({Y, Q1, cacheless_union(P, Q0, {X, P1, P0}, Q0node)});
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    store({X, cacheless_union(P1, Q1, P1node, Q1node), cacheless_union(P0, Q0, P0node, Q0node)})
	      end.


cacheless_intersect(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    cacheless_intersect(P, Q, Pnode, Qnode).

cacheless_intersect(P, Q, _, _) when P =:= 0; Q =:= 0 ->
    0;
cacheless_intersect(1, 1, _, _) ->
    1;
cacheless_intersect(P, P, _, _) ->
    P;
cacheless_intersect(P, Q, {X, P1, P0}, {Y, Q1, Q0}) ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = cacheless_intersect(P0, Q, P0node, {Y, Q1, Q0}),
                    %ets:insert(cache, {{intersect, P, Q}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = cacheless_intersect(P, Q0, {X, P1, P0}, Q0node),
		    %ets:insert(cache, {{intersect, P, Q}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, cacheless_intersect(P1, Q1, P1node, Q1node), cacheless_intersect(P0, Q0, P0node, Q0node)}),
		    %ets:insert(cache, {{intersect, P, Q}, Number}),
		    Number
	      end.


cacheless_minus(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    cacheless_minus(P, Q, Pnode, Qnode).

cacheless_minus(P, 0, _, _) ->
    P;
cacheless_minus(P, _, _, _) when P =< 1 ->
    0;
cacheless_minus(P, P, _, _) ->
    0;
cacheless_minus(P, Q, {X, P1, P0}, {Y, Q1, Q0}) ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    Number = store({X, P1, cacheless_minus(P0, Q, P0node, {Y, Q1, Q0})}),
                    %ets:insert(cache, {{minus, P, Q}, Number}),
                    Number;
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    Number = cacheless_minus(P, Q0, {X, P1, P0}, Q0node),
		    %ets:insert(cache, {{minus, P, Q}, Number}),
		    Number;
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    Number = store({X, cacheless_minus(P1, Q1, P1node, Q1node), cacheless_minus(P0, Q0, P0node, Q0node)}),
		    %ets:insert(cache, {{minus, P, Q}, Number}),
		    Number
	      end.


cacheless_subword_union(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    cacheless_subword_union(P, Q, Pnode, Qnode).

cacheless_subword_union(P, Q, _, _) when Q =< 1 ->
    P;
cacheless_subword_union(P, Q, _, _) when P =< 1 ->
    Q;
cacheless_subword_union(P, P, _, _) ->
    P;
cacheless_subword_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) ->
	    if
              X < Y ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    store({X, P1, cacheless_subword_union(P0, Q, P0node, {Y, Q1, Q0})});
	      X > Y ->
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    store({Y, Q1, cacheless_subword_union(P, Q0, {X, P1, P0}, Q0node)});
	      true ->
		    [{_, P0node}] = ets:lookup(nodememory, P0),
		    [{_, P1node}] = ets:lookup(nodememory, P1),
		    [{_, Q0node}] = ets:lookup(nodememory, Q0),
		    [{_, Q1node}] = ets:lookup(nodememory, Q1),
		    store({X, cacheless_subword_union(P1, Q1, P1node, Q1node), cacheless_subword_union(P0, Q0, P0node, Q0node)})
	      end.


cache_add(Abitlist, Bbitlist) ->
    cache_add(lists:reverse(Abitlist), lists:reverse(Bbitlist), 0, []).

cache_add([], [], _, Resultlist) ->
    Resultlist;
cache_add([0|Abits], [0|Bbits], 0, Resultlist) ->
    cache_add(Abits, Bbits, 0, [0|Resultlist]);
cache_add([Abit|Abits], [Bbit|Bbits], C, Resultlist) ->
    [{_, Anode}] = ets:lookup(nodememory, Abit),
    [{_, Bnode}] = ets:lookup(nodememory, Bbit),
    [{_, Cnode}] = ets:lookup(nodememory, C),
    {N, Carry} = cache_add(Abit, Bbit, C, Anode, Bnode, Cnode),
    cache_add(Abits, Bbits, Carry, [N|Resultlist]).

cache_add(A, A, A, _, _, _) ->
    {A, A};
cache_add(A, A, C, _, _, _) ->
    {C, A};
cache_add(A, B, B, _, _, _) ->
    {A, B};
cache_add(C, B, C, _, _, _) ->
    {B, C};
cache_add(A, B, C, _, _, _) when A =< 1, B =< 1, C =< 1 ->
    {(A+B+C) band 1, (A+B+C) bsr 1};
cache_add(A, B, C, {X, A1, A0}, {Y, B1, B0}, {Z, C1, C0}) ->
    Object = ets:lookup(cache, {add, A, B, C}),
    case Object of
      [{_, Result}] ->
        Result;
      [] ->
    if
      X < Y ->
	    if
              X < Z ->
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    {N, Carry} = cache_add(A0, B, C, A0node, {Y, B1, B0}, {Z, C1, C0}),
		    R = {store({X, A1, N}), Carry},
		    ets:insert(cache, {{add, A, B, C}, R}),
		    R;
	      Z < X ->
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {N, Carry} = cache_add(A, B, C0, {X, A1, A0}, {Y, B1, B0}, C0node),
		    R = {store({Z, C1, N}), Carry},
		    ets:insert(cache, {{add, A, B, C}, R}),
		    R;
	      true ->
		    [{_, A1node}] = ets:lookup(nodememory, A1),
		    [{_, C1node}] = ets:lookup(nodememory, C1),
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {M, Mcarry} = cache_add(A1, 0, C1, A1node, {false, 0, 0}, C1node),
		    {N, Ncarry} = cache_add(A0, B, C0, A0node, {Y, B1, B0}, C0node),
		    R = {store({X, M, N}), store({X, Mcarry, Ncarry})},
		    ets:insert(cache, {{add, A, B, C}, R}),
		    R
            end;
      Y < X ->
	    if
              Y < Z ->
		    [{_, B0node}] = ets:lookup(nodememory, B0),
		    {N, Carry} = cache_add(A, B0, C, {X, A1, A0}, B0node, {Z, C1, C0}),
		    R = {store({Y, B1, N}), Carry},
		    ets:insert(cache, {{add, A, B, C}, R}),
		    R;
	      Z < Y ->
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {N, Carry} = cache_add(A, B, C0, {X, A1, A0}, {Y, B1, B0}, C0node),
		    R = {store({Z, C1, N}), Carry},
		    ets:insert(cache, {{add, A, B, C}, R}),
		    R;
	      true ->
		    [{_, B1node}] = ets:lookup(nodememory, B1),
		    [{_, C1node}] = ets:lookup(nodememory, C1),
		    [{_, B0node}] = ets:lookup(nodememory, B0),
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {M, Mcarry} = cache_add(0, B1, C1, {false, 0, 0}, B1node, C1node),
		    {N, Ncarry} = cache_add(A, B0, C0, {X, A1, A0}, B0node, C0node),
		    R = {store({Y, M, N}), store({Y, Mcarry, Ncarry})},
		    ets:insert(cache, {{add, A, B, C}, R}),
		    R
            end;
      true ->
            if
	      X < Z ->
		    [{_, A1node}] = ets:lookup(nodememory, A1),
		    [{_, B1node}] = ets:lookup(nodememory, B1),
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    [{_, B0node}] = ets:lookup(nodememory, B0),
		    {M, Mcarry} = cache_add(A1, B1, 0, A1node, B1node, {false, 0, 0}),
		    {N, Ncarry} = cache_add(A0, B0, C, A0node, B0node, {Z, C1, C0}),
		    R = {store({X, M, N}), store({X, Mcarry, Ncarry})},
		    ets:insert(cache, {{add, A, B, C}, R}),
		    R;
	      Z < X ->
		    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {N, Carry} = cache_add(A, B, C0, {X, A1, A0}, {Y, B1, B0}, C0node),
		    R = {store({Z, C1, N}), Carry},
		    ets:insert(cache, {{add, A, B, C}, R}),
		    R;
	      true ->
		    [{_, A1node}] = ets:lookup(nodememory, A1),
		    [{_, B1node}] = ets:lookup(nodememory, B1),
                    [{_, C1node}] = ets:lookup(nodememory, C1),
		    [{_, A0node}] = ets:lookup(nodememory, A0),
		    [{_, B0node}] = ets:lookup(nodememory, B0),
                    [{_, C0node}] = ets:lookup(nodememory, C0),
		    {M, Mcarry} = cache_add(A1, B1, C1, A1node, B1node, C1node),
		    {N, Ncarry} = cache_add(A0, B0, C0, A0node, B0node, C0node),
		    R = {store({X, M, N}), store({X, Mcarry, Ncarry})},
		    ets:insert(cache, {{add, A, B, C}, R}),
		    R
            end
    end
    end.




bool_add(Abitlist, Bbitlist) ->
    bool_add(lists:reverse(Abitlist), lists:reverse(Bbitlist), 0, []).

bool_add([], [], _, Resultlist) ->
    Resultlist;
bool_add([0|Abits], [0|Bbits], 0, Resultlist) ->
    bool_add(Abits, Bbits, 0, [0|Resultlist]);
bool_add([Abit|Abits], [Bbit|Bbits], C, Resultlist) ->
    AB = intersect(Abit, Bbit),
    AxorB = exclusive_or(Abit, Bbit),
    N = exclusive_or(AxorB, C),
    Cab = intersect(AxorB, C),
    Carry = cacheless_union(AB, Cab),
    bool_add(Abits, Bbits, Carry, [N|Resultlist]).


mining_intersect(Roots, Min_sup) ->
    mining_intersect(Roots, lists:map(fun(X) -> n2node(X) end, Roots), Min_sup * length(Roots)).

mining_intersect(Ns, _, Min) when length(Ns) < Min ->
    0;
mining_intersect(Ns, Nodes, Min) ->
    A = lists:min(lists:map(fun({X, _, _}) -> X end, Nodes)),
    if
      is_boolean(A) ->
	    Length = lists:sum(Ns),
	    if
              Length < Min ->
		    0;
	      true ->
		    1
            end;
      true ->
	    {N1s, N0s, Node1s, Node0s} = childs(Ns, Nodes, A),
	    store({A, mining_intersect(N1s, Node1s, Min), mining_intersect(N0s, Node0s, Min)})
    end.


childs(Ns, Nodes, A) ->
    childs(Ns, Nodes, A, [], [], [], []).

childs([], _, _, Rn1s, Rn0s, Rnode1s, Rnode0s) ->
    {lists:reverse(Rn1s), lists:reverse(Rn0s), lists:reverse(Rnode1s), lists:reverse(Rnode0s)};
childs([_|Ns], [{A, N1, N0}|Nodes], A, Rn1s, Rn0s, Rnode1s, Rnode0s) ->
    childs(Ns, Nodes, A, [N1|Rn1s], [N0|Rn0s], [n2node(N1)|Rnode1s], [n2node(N0)|Rnode0s]);
childs([N|Ns], [{X, N1, N0}|Nodes], A, Rn1s, Rn0s, Rnode1s, Rnode0s) ->
    childs(Ns, Nodes, A, Rn1s, [N|Rn0s], Rnode1s, [{X, N1, N0}|Rnode0s]).


n2node(N) ->
    [{_, Node}] = ets:lookup(nodememory, N),
    Node.


anymiss(Root) ->
  anymiss1(Root).

anymiss1(N) when N =< 1 ->
  N;
anymiss1(N) ->
  Result = ets:lookup(cache, {anymiss, N}),
  case Result of
    [] ->
      {Much1, Much0} = anymiss0(N),
      Much = store({-1, anymiss1(Much1), Much0}),
      ets:insert(cache, {{anymiss, N}, Much}),
      Much;    
    [{_, Much}] ->
      Much
  end.

anymiss0(N) when N =< 1 ->
  {0, N};
anymiss0(N) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  {Much1, Much0} = anymiss0(N0),
  Much = store({X, anymiss1(N1), Much0}),
  {union(Much1, N1), Much}.


miss(Root, Allow) ->
  miss1(Root, Allow).

miss1(N, _) when N =< 1 ->
  N;
miss1(N, Allow) when Allow =< 0 ->
  N;
miss1(N, Allow) ->
  Result = ets:lookup(cache, {miss, N, Allow}),
  case Result of
    [] ->
      {Much1, Much0} = miss0(N, Allow),
      Much = store({-1, miss1(Much1, Allow - 1), Much0}),
      ets:insert(cache, {{miss, N, Allow}, Much}),
      Much;    
    [{_, Much}] ->
      Much
  end.

miss0(N, _) when N =< 1 ->
  {0, N};
miss0(N, Allow) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  {Much1, Much0} = miss0(N0, Allow),
  Much = store({X, miss1(N1, Allow), Much0}),
  {union(Much1, N1), Much}.


recognize(0, []) ->
  false;
recognize(1, []) ->
  true;
recognize(N, []) ->
  [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
  recognize(N0, []);
recognize(N, _) when N =< 1 ->
  false;
recognize(N, [C|Cs]) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  case X of
    -1 ->
      recognize(N1, Cs) or recognize(N0, [C|Cs]);
    C ->
      recognize(N1, Cs);
    X ->
      recognize(N0, [C|Cs])
  end.


window(N, _) when N =< 1 ->
  0;
window(N, Number) ->
  {_, N1, N0} = ets:lookup(nodememory, N),
  List = ets:lookup(nodememory, {N, window}),
  case List of
    [Number|_] ->
      0;
    List ->
      ets:insert(nodememory, {{N, window}, [Number|List]}),
      window(N1, Number) + window(N0, Number)
  end.


newid() ->
  ?I2A(ets:update_counter(nodememory, id, {2, 1})).


occur_sufdd(Sequence) ->
  Bottom = store({newid(), 1, 1}),
  ets:insert(nodememory, {{occur, Bottom}, []}),
  occur_sufdd(Sequence, 0, Bottom, Bottom).

occur_sufdd([], _, _, Root) ->
  Root;
occur_sufdd([C|Cs], Length, Tmpprefix, Tmproot) ->
  Newprefix = store({C, Tmpprefix, 1}),
  ets:insert(nodememory, {{occur, Newprefix}, [Length]}),
  Newroot = occur_union(Tmproot, Newprefix),
  occur_sufdd(Cs, Length + 1, Newprefix, Newroot).


occur_union(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    occur_union(P, Q, Pnode, Qnode).

occur_union(P, Q, _, _) when Q =< 1 ->
    P;
occur_union(P, Q, _, _) when P =< 1 ->
    Q;
occur_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P < Q ->
    Hit = ets:lookup(cache, {occur_union, P, Q}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, occur_union(P0, Q, P0node, {Y, Q1, Q0})}),
            [{_, Poccur}] = ets:lookup(nodememory, {occur, P}),
            ets:insert(nodememory, {{occur, Number}, Poccur}),
            ets:insert(cache, {{occur_union, P, Q}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, occur_union(P, Q0, {X, P1, P0}, Q0node)}),
            [{_, Qoccur}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, Qoccur}),
            ets:insert(cache, {{occur_union, P, Q}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, occur_union(P1, Q1, P1node, Q1node), occur_union(P0, Q0, P0node, Q0node)}),
            [{_, Poccurs}] = ets:lookup(nodememory, {occur, P}),
            [{_, [Qoccur]}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, [Qoccur|Poccurs]}),
            ets:insert(cache, {{occur_union, P, Q}, Number}),
            Number
          end
    end;
occur_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P > Q ->
    Hit = ets:lookup(cache, {occur_union, Q, P}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, occur_union(P0, Q, P0node, {Y, Q1, Q0})}),
            [{_, Poccur}] = ets:lookup(nodememory, {occur, P}),
            ets:insert(nodememory, {{occur, Number}, Poccur}),
            ets:insert(cache, {{occur_union, Q, P}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, occur_union(P, Q0, {X, P1, P0}, Q0node)}),
            [{_, Qoccur}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, Qoccur}),
            ets:insert(cache, {{occur_union, Q, P}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, occur_union(P1, Q1, P1node, Q1node), occur_union(P0, Q0, P0node, Q0node)}),
            [{_, Poccurs}] = ets:lookup(nodememory, {occur, P}),
            [{_, [Qoccur]}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, [Qoccur|Poccurs]}),
            ets:insert(cache, {{occur_union, Q, P}, Number}),
            Number
          end
    end;
occur_union(P, P, _, _) ->
    P.


occur_search(Root, Sequence) ->
  occur_search(Root, lists:reverse(Sequence), lists:reverse(lists:seq(0, depth(Root) - 1))).

occur_search(0, _, _) ->
  [];
occur_search(1, [], Occur) ->
  Occur;
occur_search(1, _, _) ->
  [];
occur_search(N, [], Occur) ->
  [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
  occur_search(N0, [], Occur);
occur_search(N, [C|Cs], Occur) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  case X of
    C ->
      [{_, Newoccur}] = ets:lookup(nodememory, {occur, N}),
      occur_search(N1, Cs, Newoccur);
    _ ->
      occur_search(N0, [C|Cs], Occur)
  end.


occur_intersect(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    occur_intersect(P, Q, Pnode, Qnode).

occur_intersect(P, Q, _, _) when P =:= 0; Q =:= 0 ->
    0;
occur_intersect(1, 1, _, _) ->
    1;
occur_intersect(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P < Q ->
    Hit = ets:lookup(cache, {occur_intersect, P, Q}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = occur_intersect(P0, Q, P0node, {Y, Q1, Q0}),
            ets:insert(cache, {{occur_intersect, P, Q}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = occur_intersect(P, Q0, {X, P1, P0}, Q0node),
            ets:insert(cache, {{occur_intersect, P, Q}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, occur_intersect(P1, Q1, P1node, Q1node), occur_intersect(P0, Q0, P0node, Q0node)}),
            [{_, Poccur}] = ets:lookup(nodememory, {occur, P}),
            [{_, Qoccur}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, {Poccur, Qoccur}}),
            ets:insert(cache, {{occur_intersect, P, Q}, Number}),
            Number
          end
    end;
occur_intersect(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P > Q ->
    Hit = ets:lookup(cache, {occur_intersect, Q, P}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = occur_intersect(P0, Q, P0node, {Y, Q1, Q0}),
            ets:insert(cache, {{occur_intersect, Q, P}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = occur_intersect(P, Q0, {X, P1, P0}, Q0node),
            ets:insert(cache, {{occur_intersect, Q, P}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, occur_intersect(P1, Q1, P1node, Q1node), occur_intersect(P0, Q0, P0node, Q0node)}),
            [{_, Poccur}] = ets:lookup(nodememory, {occur, P}),
            [{_, Qoccur}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, {Poccur, Qoccur}}),
            ets:insert(cache, {{occur_intersect, Q, P}, Number}),
            Number
          end
    end;
occur_intersect(P, P, _, _) ->
    P.


list_union_d_order(L1, []) ->
  L1;
list_union_d_order([], L2) ->
  L2;
list_union_d_order([C|Cs], [D|Ds]) when C > D ->
  [C|list_union_d_order(Cs, [D|Ds])];
list_union_d_order([C|Cs], [D|Ds]) when C < D ->
  [D|list_union_d_order([C|Cs], Ds)];
list_union_d_order([C|Cs], [_|Ds]) ->
  [C|list_union_d_order(Cs, Ds)].


list_pred([]) ->
  [];
list_pred([X|Xs]) when X < 1 ->
  list_pred(Xs);
list_pred([X|Xs]) ->
  [X - 1|list_pred(Xs)].


occurence_union(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    occurence_union(P, Q, Pnode, Qnode).

occurence_union(P, 0, _, _) ->
    P;
occurence_union(0, Q, _, _) ->
    Q;
occurence_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P < Q ->
    Hit = ets:lookup(cache, {occurence_union, P, Q}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, occurence_union(P0, Q, P0node, {Y, Q1, Q0})}),
            [{_, Poccur}] = ets:lookup(nodememory, {occur, P}),
            ets:insert(nodememory, {{occur, Number}, Poccur}),
            ets:insert(cache, {{occurence_union, P, Q}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, occurence_union(P, Q0, {X, P1, P0}, Q0node)}),
            [{_, Qoccur}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, Qoccur}),
            ets:insert(cache, {{occurence_union, P, Q}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, occurence_union(P1, Q1, P1node, Q1node), occurence_union(P0, Q0, P0node, Q0node)}),
            [{_, Poccur}] = ets:lookup(nodememory, {occur, P}),
            [{_, Qoccur}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, list_union_d_order(Poccur, Qoccur)}),
            ets:insert(cache, {{occurence_union, P, Q}, Number}),
            Number
          end
    end;
occurence_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P > Q ->
    Hit = ets:lookup(cache, {occurence_union, Q, P}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, occurence_union(P0, Q, P0node, {Y, Q1, Q0})}),
            [{_, Poccur}] = ets:lookup(nodememory, {occur, P}),
            ets:insert(nodememory, {{occur, Number}, Poccur}),
            ets:insert(cache, {{occurence_union, Q, P}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, occurence_union(P, Q0, {X, P1, P0}, Q0node)}),
            [{_, Qoccur}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, Qoccur}),
            ets:insert(cache, {{occurence_union, Q, P}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, occurence_union(P1, Q1, P1node, Q1node), occurence_union(P0, Q0, P0node, Q0node)}),
            [{_, Poccur}] = ets:lookup(nodememory, {occur, P}),
            [{_, Qoccur}] = ets:lookup(nodememory, {occur, Q}),
            ets:insert(nodememory, {{occur, Number}, list_union_d_order(Poccur, Qoccur)}),
            ets:insert(cache, {{occurence_union, Q, P}, Number}),
            Number
          end
    end;
occurence_union(P, P, _, _) ->
    P.


occur_anymiss(Root) ->
  occur_anymiss1(Root).

occur_anymiss1(N) when N =< 1 ->
  N;
occur_anymiss1(N) ->
  Result = ets:lookup(cache, {anymiss, N}),
  case Result of
    [] ->
      {Much1, Much0} = occur_anymiss0(N),
      Much = store({-1, occur_anymiss1(Much1), Much0}),
      ets:insert(cache, {{anymiss, N}, Much}),
      Much;    
    [{_, Much}] ->
      Much
  end.

occur_anymiss0(N) when N =< 1 ->
  {0, N};
occur_anymiss0(N) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  {Much1, Much0} = occur_anymiss0(N0),
  Much = store({X, occur_anymiss1(N1), Much0}),
  [{_, Occur}] = ets:lookup(nodememory, {occur, N}),
  ets:insert(nodememory, {{occur, Much}, Occur}),
  {occurence_union(Much1, N1), Much}.


occur_miss(Root, Allow) ->
  occur_miss1(Root, Allow).

occur_miss1(N, _) when N =< 1 ->
  N;
occur_miss1(N, Allow) when Allow =< 0 ->
  N;
occur_miss1(N, Allow) ->
  Result = ets:lookup(cache, {miss, N, Allow}),
  case Result of
    [] ->
      {Much1, Much0} = occur_miss0(N, Allow),
      Much = store({-1, occur_miss1(Much1, Allow - 1), Much0}),
      ets:insert(cache, {{miss, N, Allow}, Much}),
      Much;    
    [{_, Much}] ->
      Much
  end.

occur_miss0(N, _) when N =< 1 ->
  {0, N};
occur_miss0(N, Allow) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  {Much1, Much0} = occur_miss0(N0, Allow),
  Much = store({X, occur_miss1(N1, Allow), Much0}),
  [{_, Occur}] = ets:lookup(nodememory, {occur, N}),
  ets:insert(nodememory, {{occur, Much}, Occur}),
  {occurence_union(Much1, N1), Much}.


occurence_search(Root, Sequence) ->
  occurence_search(Root, lists:reverse(Sequence), lists:reverse(lists:seq(0, depth(Root) - 1))).

occurence_search(0, _, _) ->
  [];
occurence_search(1, [], Occur) ->
  Occur;
occurence_search(1, _, _) ->
  [];
occurence_search(N, [], Occur) ->
  [{_, {X, _, N0}}] = ets:lookup(nodememory, N),
  if
    is_atom(X) ->
      Occur;
    true ->
      occurence_search(N0, [], Occur)
  end;
occurence_search(N, [C|Cs], Occur) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  if
    X =:= -1 ->
      list_union_d_order(occurence_search(N1, Cs, list_pred(Occur)), occurence_search(N0, [C|Cs], Occur));
    X =:= C ->
      [{_, Newoccur}] = ets:lookup(nodememory, {occur, N}),
      occurence_search(N1, Cs, Newoccur);
    is_atom(X) ->
      [];
    true ->
      occurence_search(N0, [C|Cs], Occur)
  end.


window_search(N, Sequence, Allow, Width) ->
  window_search(N, lists:reverse(Sequence), Allow, Width, [], lists:reverse(lists:seq(0, depth(N) - 1))).

window_search(0, _, _, _, _, _) ->
  [];
window_search(1, [_|_], _, _, _, _) ->
  [];
window_search(1, [], _, _, _, Occur) ->
  Occur;
window_search(N, [], Allow, Interval, Misses, Occur) ->
  [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
  window_search(N0, [], Allow, Interval, Misses, Occur);
window_search(N, Sequence, Allow, Interval, [0|Nexts], Occur) ->
  window_search(N, Sequence, Allow + 1, Interval, Nexts, Occur);
window_search(N, [C|Cs], Allow, Interval, [], Occur) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  if
    X =:= -1 , Allow >= 1 ->
      list_union_d_order(window_search(N1, Cs, Allow - 1, 1, [Interval - 1], list_pred(Occur)), 
        window_search(N0, [C|Cs], Allow, Interval, [], Occur));
    is_atom(X) ->
      [];
    X < C ->
      window_search(N0, [C|Cs], Allow, Interval, [], Occur);
    X > C ->
      [];
    true ->
      [{_, Newoccur}] = ets:lookup(nodememory, {occur, N}),
      window_search(N1, Cs, Allow, Interval, [], Newoccur)
  end;
window_search(N, [C|Cs], Allow, Interval, [Last|Nexts], Occur) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  if
    X =:= -1 , Allow >= 1 ->
      list_union_d_order(window_search(N1, Cs, Allow - 1, 1, [Last - 1|Nexts] ++ [Interval], list_pred(Occur)), 
        window_search(N0, [C|Cs], Allow, Interval, [Last|Nexts], Occur));
    is_atom(X) ->
      [];
    X < C ->
      window_search(N0, [C|Cs], Allow, Interval, [Last|Nexts], Occur);
    X > C ->
      [];
    true ->
      [{_, Newoccur}] = ets:lookup(nodememory, {occur, N}),
      window_search(N1, Cs, Allow, Interval + 1, [Last - 1|Nexts], Newoccur)
  end.


window_miss(Root, Domain, Allow, Width) ->
  window_miss1(Root, Domain, Allow, Width, [], lists:reverse(lists:seq(0, depth(Root) - 1))).

window_miss1(N, _, _, _, _, _) when N =< 1 ->
 N;
window_miss1(N, Domain, Allow, Interval, [0|Nexts], Occur) ->
  window_miss1(N, Domain, Allow + 1, Interval, Nexts, Occur);
window_miss1(N, Domain, Allow, Interval, Misses, _) when Allow < 1 ->
  Result = ets:lookup(cache, {window_miss, N, [Interval|Misses]}),
  case Result of
    [] ->
      [{_, {X, _, _}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          Window = window_miss0(N, Domain, Allow, Interval, Misses, [], Domain, 0),
          ets:insert(cache, {{window_miss, N, [Interval|Misses]}, Window}),
          Window
      end;
    [{_, Window}] ->
      Window
  end;
window_miss1(N, Domain, Allow, Interval, [], Occur) ->
  Result = ets:lookup(cache, {window_miss, N, [Interval]}),
  case Result of
    [] ->
      [{_, {X, _, _}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          Descendant = descendant(N),
          Newoccur = list_pred(Occur),
          Miss = window_miss1(Descendant, Domain, Allow - 1, 1, [Interval - 1], Newoccur),
          Window = window_miss0(N, Domain, Allow, Interval, [], Newoccur, Domain, Miss),
          ets:insert(cache, {{window_miss, N, [Interval]}, Window}),
          Window
      end;
    [{_, Window}] ->
      Window
  end;
window_miss1(N, Domain, Allow, Interval, [Last|Nexts], Occur) ->
  Result = ets:lookup(cache, {window_miss, N, [Interval|[Last|Nexts]]}),
  case Result of
    [] ->
      [{_, {X, _, _}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          Descendant = descendant(N),
          Newoccur = list_pred(Occur),
          Miss = window_miss1(Descendant, Domain, Allow - 1, 1, [Last - 1|Nexts] ++ [Interval], Newoccur),
          Window = window_miss0(N, Domain, Allow, Interval, [Last|Nexts], Newoccur, Domain, Miss),
          ets:insert(cache, {{window_miss, N, [Interval|[Last|Nexts]]}, Window}),
          Window
      end;
    [{_, Window}] ->
      Window
  end.

window_miss0(N, _, _, _, _, _, [], _) ->
  N;
window_miss0(N, Domain, Allow, Interval, [], Occur, [C|Cs], Miss) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  if
    C < X ->
      New = store({C, Miss, window_miss0(N, Domain, Allow, Interval, [], Occur, Cs, Miss)}),
      if
        Miss =:= 0 ->
          ok;
        true ->
          ets:insert(nodememory, {{occur, New}, Occur})
      end,
      New;
    true ->
      [{_, Myoccur}] = ets:lookup(nodememory, {occur, N}),
      Child = window_miss1(N1, Domain, Allow, Interval, [], Myoccur),
      Newmiss = occurence_union(Miss, Child),
      New = store({X, Newmiss, window_miss0(N0, Domain, Allow, Interval, [], Occur, Cs, Miss)}),
      if
        Occur =:= [] ->
          Newoccur = Myoccur;
        true ->
          Newoccur = Occur
      end,
      ets:insert(nodememory, {{occur, New}, Newoccur}),
      New
  end;
window_miss0(N, Domain, Allow, Interval, [Last|Nexts], Occur, [C|Cs], Miss) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  if
    C < X ->
      New = store({C, Miss, window_miss0(N, Domain, Allow, Interval, [Last|Nexts], Occur, Cs, Miss)}),
      if
        Miss =:= 0 ->
          ok;
        true ->
          ets:insert(nodememory, {{occur, New}, Occur})
      end,
      New;
    true ->
      [{_, Myoccur}] = ets:lookup(nodememory, {occur, N}),
      Child = window_miss1(N1, Domain, Allow, Interval + 1, [Last - 1|Nexts], Myoccur),
      Newmiss = occurence_union(Miss, Child),
      New = store({X, Newmiss, window_miss0(N0, Domain, Allow, Interval, [Last|Nexts], Occur, Cs, Miss)}),
      if
        Occur =:= [] ->
          Newoccur = Myoccur;
        true ->
          Newoccur = Occur
      end,
      ets:insert(nodememory, {{occur, New}, Newoccur}),
      New
  end.


descendant(N) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  if
    is_atom(X) ->
      0;
    true ->
      occurence_union(N1, descendant(N0))
  end.


refer(N) when N =< 1 ->
  ok;
refer(N) ->
  [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
  Ref = ets:lookup(reference, N),
  case Ref of
    [] ->
      ets:insert(reference, {N, 1}),
      refer(N1),
      refer(N0);
    _ ->
      ets:update_counter(reference, N, {2, 1}),
      ok
  end.

intersect_r_maximal(S, T, Rprefix) ->
  P = search_node(S, Rprefix),
  Q = search_node(T, Rprefix),
  I = intersect(P, Q),
  Prefix = lists:reverse(Rprefix),
  if
    I =:= 1 ->
      io:format("~s ~p\n", [Prefix, {occur_search(S, Prefix), occur_search(T, Prefix)}]);
    true ->
      intersect_r_maximal(I, P, Q, n2node(I), n2node(P), n2node(Q), Prefix)
  end.

intersect_r_maximal(N, _, _, _, _, _, _) when N =< 1 ->
  ok;
intersect_r_maximal(N, _, Q, {X, N1, N0}, {Y, _, P0}, {Z, Q1, Q0}, Suffix) when Y < X ->
  intersect_r_maximal(N, P0, Q, {X, N1, N0}, n2node(P0), {Z, Q1, Q0}, Suffix);
intersect_r_maximal(N, P, _, {X, N1, N0}, {Y, P1, P0}, {Z, _, Q0}, Suffix) when Z < X ->
  intersect_r_maximal(N, P, Q0, {X, N1, N0}, {Y, P1, P0}, n2node(Q0), Suffix);
intersect_r_maximal(_, P, Q, {X, N1, N0}, {_, P1, P0}, {_, Q1, Q0}, Suffix) ->
  if
    N1 =:= 1 ->
      [{_, Poccur}] = ets:lookup(nodememory, {occur, P}),
      [{_, Qoccur}] = ets:lookup(nodememory, {occur, Q}),
      io:format("~s ~p\n", [[X|Suffix], {Poccur, Qoccur}]),
      intersect_r_maximal(N0, P0, Q0, n2node(N0), n2node(P0), n2node(Q0), Suffix);
    true ->
      intersect_r_maximal(N1, P1, Q1, n2node(N1), n2node(P1), n2node(Q1), [X|Suffix]),
      intersect_r_maximal(N0, P0, Q0, n2node(N0), n2node(P0), n2node(Q0), Suffix)
  end.


find_right(I, Os, Ot) ->
  find_right(I, Os, Ot, []).

find_right(N, _, _, _) when N =< 1 ->
  ok;
find_right(N, Os, Ot, Right) ->
  Already = ets:lookup(reference, {right, N}),
  case Already of
    [] ->
      ets:insert(reference, {{right, N}, ok}),
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      [{_, Ref}] = ets:lookup(reference, N),
      D = depth(N0),
      if
        N1 =:= 1 , Ref =:= 1 , D =< 1 ->
io:format("Call ~s at ~p\n", [[X|Right], N]),
          intersect_r_maximal(Os, Ot, [X|Right]),
          find_right(N0, Os, Ot, Right);
        N1 =:= 1 , D =< 1 ->
io:format("Call ~s at ~p\n", [[X], N]),
          intersect_r_maximal(Os, Ot, [X]),
          find_right(N0, Os, Ot, []);
        Ref =:= 1 ->
          find_right(N1, Os, Ot, [X|Right]),
          find_right(N0, Os, Ot, Right);
        true ->
          find_right(N1, Os, Ot, [X]),
          find_right(N0, Os, Ot, [])
      end,
      ok;
    _ ->
      ok
  end.


s_maximal(Sequence1, Sequence2) ->
  s_maximal(occur_sufdd(Sequence1), occur_sufdd(Sequence2), sufdd(Sequence1), sufdd(Sequence2)).

s_maximal(Os, Ot, S, T) ->
  I = intersect(S, T),
  ets:new(reference, [private, named_table]),
  refer(I),
  find_right(I, Os, Ot),
  one_letter(I, Os, Ot),
  ets:delete(reference),
  ok.


one_letter(N, _, _) when N =< 1 ->
  ok;
one_letter(N, Os, Ot) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  case N1 of
    1 ->
      io:format("~s ~p\n", [[X], {occur_search(Os, [X]), occur_search(Ot, [X])}]),
      one_letter(N0, Os, Ot);
    _ ->
      one_letter(N0, Os, Ot)
  end.


maximal(Sequence1, Sequence2) ->
  maximal(Sequence1, Sequence2, -1).

maximal(Sequence1, Sequence2, Min) ->
  S1 = sufdd(Sequence1),
  S2 = sufdd(Sequence2),
  O1 = occur_sufdd(Sequence1),
  O2 = occur_sufdd(Sequence2),
%io:format("SuffixDDs are computed!\n", []),
  maximal(intersect(S1, S2), O1, O2, Min).

maximal(N, _, _, _) when N =< 1 ->
  [];
maximal(N, O1, O2, Min) ->
  D = depth(N),
  if
    D < Min ->
      [];
    true ->
      L = longest(N),
      [{L, {occur_search(O1, L), occur_search(O2, L)}}|maximal(minus(N, sufdd(L)), O1, O2, Min)]
  end.


%max(N) ->
%  depth(N),
%  max(N, []).
%
%max(N, Rsequence) when N =< 1 ->
%  lists:reverse(Rsequence);
%max(N, Rsequence) ->
%    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
%    [{_, Length0}] = ets:lookup(cache, {depth, N0}),
%    [{_, Length1}] = ets:lookup(cache, {depth, N1}),
%    if
%      Length0 > Length1 + 1 ->
%        max(N0, Rsequence);
%      true ->
%        max(N1, [X|Rsequence])
%    end.


super_maximal(Sequence1, Sequence2) ->
  super_maximal(Sequence1, Sequence2, -1).

super_maximal(Sequence1, Sequence2, Min) ->
  O1 = occur_sufdd(Sequence1),
  O2 = occur_sufdd(Sequence2),
%io:format("SuffixDDs are computed!\n", []),
  super_maximal(intersect(O1, O2), O1, O2, Min).

super_maximal(N, _, _, _) when N =< 1 ->
  [];
super_maximal(N, O1, O2, Min) ->
  D = depth(N),
  if
    D < Min ->
      [];
    true ->
      Ls = longest(N),
      super_maximal(N, O1, O2, Min, Ls)
  end.

super_maximal(N, O1, O2, Min, []) ->
  super_maximal(N, O1, O2, Min);
super_maximal(N, O1, O2, Min, [S|Ss]) ->
  R = lists:reverse(S),
  [{R, {occur_search(O1, R), occur_search(O2, R)}}|super_maximal(minus(N, sufdd(S)), O1, O2, Min, Ss)].











































p_subword_union(P, Q, Id) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    p_subword_union(P, Q, Pnode, Qnode, Id).

p_subword_union(P, Q, _, _, _) when Q =< 1 ->
    P;
p_subword_union(P, Q, _, _, _) when P =< 1 ->
    Q;
p_subword_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}, Id) when P < Q ->
    Hit = ets:lookup(cache, {p_union, P, Q}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, p_subword_union(P0, Q, P0node, {Y, Q1, Q0}, Id)}),
            [{_, [{_, Poccur}]}] = ets:lookup(nodememory, {location, P}),
            ets:insert(nodememory, {{location, Number}, [{Id, Poccur}]}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            ets:insert(nodememory, {{freq, Number}, Pfreq}),
            ets:insert(cache, {{p_union, P, Q}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, p_subword_union(P, Q0, {X, P1, P0}, Q0node, Id)}),
            [{_, [{_, Qoccur}]}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, [{Id, Qoccur}]}),
            ets:insert(nodememory, {{freq, Number}, 1}),
            ets:insert(cache, {{p_union, P, Q}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, p_subword_union(P1, Q1, P1node, Q1node, Id), p_subword_union(P0, Q0, P0node, Q0node, Id)}),
            [{_, [{_, Poccurs}]}] = ets:lookup(nodememory, {location, P}),
            [{_, [{_, [Qoccur]}]}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, [{Id, [Qoccur|Poccurs]}]}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            ets:insert(nodememory, {{freq, Number}, Pfreq + 1}),
            ets:insert(cache, {{p_union, P, Q}, Number}),
            Number
          end
    end;
p_subword_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}, Id) when P > Q ->
    Hit = ets:lookup(cache, {p_union, Q, P}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, p_subword_union(P0, Q, P0node, {Y, Q1, Q0}, Id)}),
            [{_, [{_, Poccur}]}] = ets:lookup(nodememory, {location, P}),
            ets:insert(nodememory, {{location, Number}, [{Id, Poccur}]}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            ets:insert(nodememory, {{freq, Number}, Pfreq}),
            ets:insert(cache, {{p_union, Q, P}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, p_subword_union(P, Q0, {X, P1, P0}, Q0node, Id)}),
            [{_, [{_, Qoccur}]}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, [{Id, Qoccur}]}),
            ets:insert(nodememory, {{freq, Number}, 1}),
            ets:insert(cache, {{p_union, Q, P}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, p_subword_union(P1, Q1, P1node, Q1node, Id), p_subword_union(P0, Q0, P0node, Q0node, Id)}),
            [{_, [{_, Poccurs}]}] = ets:lookup(nodememory, {location, P}),
            [{_, [{_, [Qoccur]}]}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, [{Id, [Qoccur|Poccurs]}]}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            ets:insert(nodememory, {{freq, Number}, Pfreq + 1}),
            ets:insert(cache, {{p_union, Q, P}, Number}),
            Number
          end
    end;
p_subword_union(P, P, _, _, _) ->
    P.


p_sufdd(Sequence) ->
  Id = newid(),
  Bottom = store({Id, 1, 1}),
  ets:insert(nodememory, {{location, Bottom}, [{Id, lists:reverse(lists:seq(0, length(Sequence)))}]}),
  ets:insert(nodememory, {{freq, Bottom}, 0}),
  p_sufdd(Sequence, 0, Bottom, Bottom, Id).

p_sufdd([], _, _, Root, _) ->
  Root;
p_sufdd([C|Cs], Length, Tmpprefix, Tmproot, Id) ->
  Newprefix = store({C, Tmpprefix, 1}),
  ets:insert(nodememory, {{location, Newprefix}, [{Id, [Length]}]}),
  ets:insert(nodememory, {{freq, Newprefix}, 1}),
  Newroot = p_subword_union(Tmproot, Newprefix, Id),
  p_sufdd(Cs, Length + 1, Newprefix, Newroot, Id).


all_location(Root) ->
  all_location(Root, []).

all_location(N, Result) when N =< 1 ->
  Result;
all_location(N, Prev) ->
  [{_, {X, _, N0}}] = ets:lookup(nodememory, N),
  if
    is_atom(X) ->
      [{_, [Location]}] = ets:lookup(nodememory, {location, N}),
      all_location(N0, [Location|Prev]);
    true ->
      all_location(N0, Prev)
  end.


p_search(Root, Sequence) ->
  All = all_location(Root),
  p_search(Root, lists:reverse(Sequence), All).

p_search(0, _, _) ->
  [];
p_search(1, [], Location) ->
  Location;
p_search(1, _, _) ->
  [];
p_search(N, [], Location) ->
  [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
  p_search(N0, [], Location);
p_search(N, [C|Cs], Location) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  case X of
    C ->
      [{_, Newoccur}] = ets:lookup(nodememory, {location, N}),
      [{_, Freq}] = ets:lookup(nodememory, {freq, N}),
      p_search(N1, Cs, {Freq, Newoccur});
    _ ->
      p_search(N0, [C|Cs], Location)
  end.


p_union(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    p_union(P, Q, Pnode, Qnode).

p_union(P, 0, _, _) ->
    P;
p_union(0, Q, _, _) ->
    Q;
p_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P < Q ->
    Hit = ets:lookup(cache, {p_union, P, Q}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, p_union(P0, Q, P0node, {Y, Q1, Q0})}),
            [{_, Poccur}] = ets:lookup(nodememory, {location, P}),
            ets:insert(nodememory, {{location, Number}, Poccur}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            ets:insert(nodememory, {{freq, Number}, Pfreq}),
            ets:insert(cache, {{p_union, P, Q}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, p_union(P, Q0, {X, P1, P0}, Q0node)}),
            [{_, Qoccur}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, Qoccur}),
            [{_, Qfreq}] = ets:lookup(nodememory, {freq, Q}),
            ets:insert(nodememory, {{freq, Number}, Qfreq}),
            ets:insert(cache, {{p_union, P, Q}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, p_union(P1, Q1, P1node, Q1node), p_union(P0, Q0, P0node, Q0node)}),
            [{_, [{Id, Poccur}]}] = ets:lookup(nodememory, {location, P}),
            [{_, [{_, Qoccur}]}] = ets:lookup(nodememory, {location, Q}),
            Newoccur = list_union_d_order(Poccur, Qoccur),
            ets:insert(nodememory, {{location, Number}, [{Id, Newoccur}]}),
            ets:insert(nodememory, {{freq, Number}, length(Newoccur)}),
            ets:insert(cache, {{p_union, P, Q}, Number}),
            Number
          end
    end;
p_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P > Q ->
    Hit = ets:lookup(cache, {p_union, Q, P}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, p_union(P0, Q, P0node, {Y, Q1, Q0})}),
            [{_, Poccur}] = ets:lookup(nodememory, {location, P}),
            ets:insert(nodememory, {{location, Number}, Poccur}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            ets:insert(nodememory, {{freq, Number}, Pfreq}),
            ets:insert(cache, {{p_union, Q, P}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, p_union(P, Q0, {X, P1, P0}, Q0node)}),
            [{_, Qoccur}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, Qoccur}),
            [{_, Qfreq}] = ets:lookup(nodememory, {freq, Q}),
            ets:insert(nodememory, {{freq, Number}, Qfreq}),
            ets:insert(cache, {{p_union, Q, P}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, p_union(P1, Q1, P1node, Q1node), p_union(P0, Q0, P0node, Q0node)}),
            [{_, [{Id, Poccur}]}] = ets:lookup(nodememory, {location, P}),
            [{_, [{_, Qoccur}]}] = ets:lookup(nodememory, {location, Q}),
            Newoccur = list_union_d_order(Poccur, Qoccur),
            ets:insert(nodememory, {{location, Number}, [{Id, Newoccur}]}),
            ets:insert(nodememory, {{freq, Number}, length(Newoccur)}),
            ets:insert(cache, {{p_union, Q, P}, Number}),
            Number
          end
    end;
p_union(P, P, _, _) ->
    P.


p_w_miss(Root, Domain, Allow, Width) ->
  [{Id, Occur}] = all_location(Root),
  p_w_miss1(Root, Domain, Allow, Width, [], Occur, Id, length(Occur)).

p_w_miss1(N, _, _, _, _, _, _, _) when N =< 1 ->
 N;
p_w_miss1(N, Domain, Allow, Interval, [0|Nexts], Occur, Id, Freq) ->
  p_w_miss1(N, Domain, Allow + 1, Interval, Nexts, Occur, Id, Freq);
p_w_miss1(N, Domain, Allow, Interval, Misses, _, Id, _) when Allow < 1 ->
  Result = ets:lookup(cache, {p_w_miss, N, [Interval|Misses]}),
  case Result of
    [] ->
      [{_, {X, _, _}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          Window = p_w_miss0(N, Domain, Allow, Interval, Misses, [], Domain, 0, Id, 0),
          ets:insert(cache, {{p_w_miss, N, [Interval|Misses]}, Window}),
          Window
      end;
    [{_, Window}] ->
      Window
  end;
p_w_miss1(N, Domain, Allow, Interval, [], Occur, Id, Freq) ->
  Result = ets:lookup(cache, {p_w_miss, N, [Interval]}),
  case Result of
    [] ->
      [{_, {X, _, _}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          Descendant = p_low(N),
          Newoccur = list_pred(Occur),
          Miss = p_w_miss1(Descendant, Domain, Allow - 1, 1, [Interval - 1], Newoccur, Id, length(Newoccur)),
          Window = p_w_miss0(N, Domain, Allow, Interval, [], Newoccur, Domain, Miss, Id, Freq),
          ets:insert(cache, {{p_w_miss, N, [Interval]}, Window}),
          Window
      end;
    [{_, Window}] ->
      Window
  end;
p_w_miss1(N, Domain, Allow, Interval, [Last|Nexts], Occur, Id, Freq) ->
  Result = ets:lookup(cache, {p_w_miss, N, [Interval|[Last|Nexts]]}),
  case Result of
    [] ->
      [{_, {X, _, _}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          Descendant = p_low(N),
          Newoccur = list_pred(Occur),
          Miss = p_w_miss1(Descendant, Domain, Allow - 1, 1, [Last - 1|Nexts] ++ [Interval], Newoccur, Id, length(Newoccur)),
          Window = p_w_miss0(N, Domain, Allow, Interval, [Last|Nexts], Newoccur, Domain, Miss, Id, Freq),
          ets:insert(cache, {{p_w_miss, N, [Interval|[Last|Nexts]]}, Window}),
          Window
      end;
    [{_, Window}] ->
      Window
  end.

p_w_miss0(N, _, _, _, _, _, [], _, _, _) ->
  N;
p_w_miss0(N, Domain, Allow, Interval, [], Occur, [C|Cs], Miss, Id, Freq) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  if
    C < X ->
      New = store({C, Miss, p_w_miss0(N, Domain, Allow, Interval, [], Occur, Cs, Miss, Id, Freq)}),
      if
        Miss =:= 0 ->
          ok;
        true ->
          ets:insert(nodememory, {{location, New}, [{Id, Occur}]}),
          ets:insert(nodememory, {{freq, New}, Freq})
      end,
      New;
    true ->
      [{_, [{_, Myoccur}]}] = ets:lookup(nodememory, {location, N}),
      Child = p_w_miss1(N1, Domain, Allow, Interval, [], Myoccur, Id, length(Myoccur)),
      Newmiss = p_union(Miss, Child),
      New = store({X, Newmiss, p_w_miss0(N0, Domain, Allow, Interval, [], Occur, Cs, Miss, Id, Freq)}),
      if
        Occur =:= [] ->
          Newoccur = Myoccur;
        true ->
          Newoccur = Occur
      end,
      ets:insert(nodememory, {{location, New}, [{Id, Newoccur}]}),
      ets:insert(nodememory, {{freq, New}, length(Newoccur)}),
      New
  end;
p_w_miss0(N, Domain, Allow, Interval, [Last|Nexts], Occur, [C|Cs], Miss, Id, Freq) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  if
    C < X ->
      New = store({C, Miss, p_w_miss0(N, Domain, Allow, Interval, [Last|Nexts], Occur, Cs, Miss, Id, Freq)}),
      if
        Miss =:= 0 ->
          ok;
        true ->
          ets:insert(nodememory, {{location, New}, [{Id, Occur}]}),
          ets:insert(nodememory, {{freq, New}, Freq})
      end,
      New;
    true ->
      [{_, [{_, Myoccur}]}] = ets:lookup(nodememory, {location, N}),
      Child = p_w_miss1(N1, Domain, Allow, Interval + 1, [Last - 1|Nexts], Myoccur, Id, length(Myoccur)),
      Newmiss = p_union(Miss, Child),
      New = store({X, Newmiss, p_w_miss0(N0, Domain, Allow, Interval, [Last|Nexts], Occur, Cs, Miss, Id, Freq)}),
      if
        Occur =:= [] ->
          Newoccur = Myoccur;
        true ->
          Newoccur = Occur
      end,
      ets:insert(nodememory, {{location, New}, [{Id, Newoccur}]}),
      ets:insert(nodememory, {{freq, New}, length(Newoccur)}),
      New
  end.


p_low(N) ->
  [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
  if
    is_atom(X) ->
      0;
    true ->
      p_union(N1, p_low(N0))
  end.


p_id_union(P, Q) ->
    [{_, Pnode}] = ets:lookup(nodememory, P),
    [{_, Qnode}] = ets:lookup(nodememory, Q),
    p_id_union(P, Q, Pnode, Qnode).

p_id_union(P, 0, _, _) ->
    P;
p_id_union(0, Q, _, _) ->
    Q;
p_id_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P < Q ->
    Hit = ets:lookup(cache, {p_union, P, Q}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, p_id_union(P0, Q, P0node, {Y, Q1, Q0})}),
            [{_, Poccur}] = ets:lookup(nodememory, {location, P}),
            ets:insert(nodememory, {{location, Number}, Poccur}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            ets:insert(nodememory, {{freq, Number}, Pfreq}),
            ets:insert(cache, {{p_union, P, Q}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, p_id_union(P, Q0, {X, P1, P0}, Q0node)}),
            [{_, Qoccur}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, Qoccur}),
            [{_, Qfreq}] = ets:lookup(nodememory, {freq, Q}),
            ets:insert(nodememory, {{freq, Number}, Qfreq}),
            ets:insert(cache, {{p_union, P, Q}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, p_id_union(P1, Q1, P1node, Q1node), p_id_union(P0, Q0, P0node, Q0node)}),
            [{_, Plocations}] = ets:lookup(nodememory, {location, P}),
            [{_, [Qlocation]}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, [Qlocation|Plocations]}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            [{_, Qfreq}] = ets:lookup(nodememory, {freq, Q}),
            ets:insert(nodememory, {{freq, Number}, Pfreq + Qfreq}),
            ets:insert(cache, {{p_union, P, Q}, Number}),
            Number
          end
    end;
p_id_union(P, Q, {X, P1, P0}, {Y, Q1, Q0}) when P > Q ->
    Hit = ets:lookup(cache, {p_union, Q, P}),
    case Hit of
      [{_, Result}] ->
        Result;
      _ ->
        if
          X < Y ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            Number = store({X, P1, p_id_union(P0, Q, P0node, {Y, Q1, Q0})}),
            [{_, Poccur}] = ets:lookup(nodememory, {location, P}),
            ets:insert(nodememory, {{location, Number}, Poccur}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            ets:insert(nodememory, {{freq, Number}, Pfreq}),
            ets:insert(cache, {{p_union, Q, P}, Number}),
            Number;
          X > Y ->
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            Number = store({Y, Q1, p_id_union(P, Q0, {X, P1, P0}, Q0node)}),
            [{_, Qoccur}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, Qoccur}),
            [{_, Qfreq}] = ets:lookup(nodememory, {freq, Q}),
            ets:insert(nodememory, {{freq, Number}, Qfreq}),
            ets:insert(cache, {{p_union, Q, P}, Number}),
            Number;
          true ->
            [{_, P0node}] = ets:lookup(nodememory, P0),
            [{_, P1node}] = ets:lookup(nodememory, P1),
            [{_, Q0node}] = ets:lookup(nodememory, Q0),
            [{_, Q1node}] = ets:lookup(nodememory, Q1),
            Number = store({X, p_id_union(P1, Q1, P1node, Q1node), p_id_union(P0, Q0, P0node, Q0node)}),
            [{_, Plocations}] = ets:lookup(nodememory, {location, P}),
            [{_, [Qlocation]}] = ets:lookup(nodememory, {location, Q}),
            ets:insert(nodememory, {{location, Number}, [Qlocation|Plocations]}),
            [{_, Pfreq}] = ets:lookup(nodememory, {freq, P}),
            [{_, Qfreq}] = ets:lookup(nodememory, {freq, Q}),
            ets:insert(nodememory, {{freq, Number}, Pfreq + Qfreq}),
            ets:insert(cache, {{p_union, Q, P}, Number}),
            Number
          end
    end;
p_id_union(P, P, _, _) ->
    P.


db_create(Sequences, Domain, Allow, Width) ->
  db_create(Sequences, Domain, Allow, Width, 0).

db_create([], _, _, _, Root) ->
  Root;
db_create([W|Ws], Domain, Allow, Width, Tmproot) ->
  S = p_sufdd(W),
  T = p_w_miss(S, Domain, Allow, Width),
  db_create(Ws, Domain, Allow, Width, p_id_union(Tmproot, T)).


p_w_miss_a(Root, Allow, Width) ->
  [{Id, Occur}] = all_location(Root),
  p_w_miss_a1(Root, Allow, Width, [], Occur, Id).

p_w_miss_a1(N, _, _, _, _, _) when N =< 1 ->
  N;
p_w_miss_a1(N, Allow, Interval, [0|Nexts], Occur, Id) ->
  p_w_miss_a1(N, Allow + 1, Interval, Nexts, Occur, Id);
p_w_miss_a1(N, Allow, Interval, Zone, _, _) when Allow < 1 ->
      [{_, {X, _, _}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          p_w_miss_a0(N, Allow, Interval, Zone)
      end;
p_w_miss_a1(N, Allow, Interval, [], Occur, Id) ->
      [{_, {X, _, _}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          Newoccur = list_pred(Occur),
          Newsize = length(Newoccur),
          New = store({-1, p_w_miss_a1(p_low(N), Allow - 1, 1, [Interval - 1], Newoccur, Id), p_w_miss_a0(N, Allow, Interval, [])}),
          ets:insert(nodememory, {{location, New}, [{Id, Newoccur}]}),
          ets:insert(nodememory, {{freq, New}, Newsize}),
          New
      end;
p_w_miss_a1(N, Allow, Interval, [Last|Nexts], Occur, Id) ->
      [{_, {X, _, _}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          Newoccur = list_pred(Occur),
          Newsize = length(Newoccur),
          New = store({-1, p_w_miss_a1(p_low(N), Allow - 1, 1, [Last - 1|Nexts] ++ [Interval], Newoccur, Id), p_w_miss_a0(N, Allow, Interval, [Last|Nexts])}),
          ets:insert(nodememory, {{location, New}, [{Id, Newoccur}]}),
          ets:insert(nodememory, {{freq, New}, Newsize}),
          New
      end.


p_w_miss_a0(N, _, _, _) when N =< 1 ->
  N;
p_w_miss_a0(N, Allow, Interval, []) ->
  Result = ets:lookup(cache, {p_w_miss_a, N, [Interval]}),
  case Result of
    [] ->
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          [{_, [{Id, Occur}]}] = ets:lookup(nodememory, {location, N}),
          [{_, Freq}] = ets:lookup(nodememory, {freq, N}),
          New = store({X, p_w_miss_a1(N1, Allow, Interval, [], Occur, Id), p_w_miss_a0(N0, Allow, Interval, [])}),
          ets:insert(nodememory, {{location, New}, [{Id, Occur}]}),
          ets:insert(nodememory, {{freq, New}, Freq}),
          ets:insert(cache, {{p_w_miss_a, N, [Interval]}, New}),
          New
      end;
    [{_, A}] ->
      A
  end;
p_w_miss_a0(N, Allow, Interval, [Last|Nexts]) ->
  Result = ets:lookup(cache, {p_w_miss_a, N, [Interval|[Last|Nexts]]}),
  case Result of
    [] ->
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      if
        is_atom(X) ->
          N;
        true ->
          [{_, [{Id, Occur}]}] = ets:lookup(nodememory, {location, N}),
          [{_, Freq}] = ets:lookup(nodememory, {freq, N}),
          New = store({X, p_w_miss_a1(N1, Allow, Interval + 1, [Last - 1|Nexts], Occur, Id), p_w_miss_a0(N0, Allow, Interval, [Last|Nexts])}),
          ets:insert(nodememory, {{location, New}, [{Id, Occur}]}),
          ets:insert(nodememory, {{freq, New}, Freq}),
          ets:insert(cache, {{p_w_miss_a, N, [Interval|[Last|Nexts]]}, New}),
          New
      end;
    [{_, A}] ->
      A
  end.


p_list_union([], L2) ->
  L2;
p_list_union(L1, []) ->
  L1;
p_list_union([{Id1, Occur1}|L1], [{Id2, Occur2}|L2]) ->
  if
    Id1 > Id2 ->
      [{Id1, Occur1}|p_list_union(L1, [{Id2, Occur2}|L2])];
    Id1 < Id2 ->
      [{Id2, Occur2}|p_list_union([{Id1, Occur1}|L1], L2)];
    true ->
      [{Id1, list_union_d_order(Occur1, Occur2)}|p_list_union(L1, L2)]
  end.


p_search_a(Root, Sequence) ->
  Location = all_location(Root),
  ets:new(p_s, [private, named_table]),
  Result = p_search_a(Root, lists:reverse(Sequence), Location, 0),
  ets:delete(p_s),
  {lists:sum(lists:map(fun({_, List}) -> length(List) end, Result)), Result}.

p_search_a(0, _, _, _) ->
  [];
p_search_a(1, [], Location, _) ->
  Location;
p_search_a(1, _, _, _) ->
  [];
p_search_a(N, [], Location, Index) ->
  Result = ets:lookup(p_s, {N, Index}),
  case Result of
    [] ->
      [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
      Get = p_search_a(N0, [], Location, Index),
      ets:insert(p_s, {{N, Index}, []}),
      Get;
    _ ->
      []
  end;
p_search_a(N, [C|Cs], Location, Index) ->
Result = ets:lookup(p_s, {N, Index}),
case Result of
  [] ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    if
      X =:= -1 ->
        [{_, Mylocation}] = ets:lookup(nodememory, {location, N}),
        Get = p_list_union(p_search_a(N1, Cs, Mylocation, Index + 1), p_search_a(N0, [C|Cs], Location, Index)),
        ets:insert(p_s, {{N, Index}, []}),
        Get;
      X < C ->
        Get = p_search_a(N0, [C|Cs], Location, Index),
        ets:insert(p_s, {{N, Index}, []}),
        Get;
      X > C ->
        [];
      true ->
        [{_, Mylocation}] = ets:lookup(nodememory, {location, N}),
        Get = p_search_a(N1, Cs, Mylocation, Index + 1),
        ets:insert(p_s, {{N, Index}, []}),
        Get
    end;
  _ ->
    []
  end.


p_search_an(Root, Sequence) ->
  Location = all_location(Root),
  Result = p_search_an(Root, lists:reverse(Sequence), Location),
  {lists:sum(lists:map(fun({_, List}) -> length(List) end, Result)), Result}.

p_search_an(0, _, _) ->
  [];
p_search_an(1, [], Location) ->
  Location;
p_search_an(1, _, _) ->
  [];
p_search_an(N, [], Location) ->
      [{_, {_, _, N0}}] = ets:lookup(nodememory, N),
      p_search_an(N0, [], Location);
p_search_an(N, [C|Cs], Location) ->
    [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
    if
      X =:= -1 ->
        [{_, Mylocation}] = ets:lookup(nodememory, {location, N}),
        p_list_union(p_search_an(N1, Cs, Mylocation), p_search_an(N0, [C|Cs], Location));
      X < C ->
        p_search_an(N0, [C|Cs], Location);
      X > C ->
        [];
      true ->
        [{_, Mylocation}] = ets:lookup(nodememory, {location, N}),
        p_search_an(N1, Cs, Mylocation)
    end.


db_create_a(Sequences, Allow, Width) ->
  db_create_a(Sequences, Allow, Width, 0).

db_create_a([], _, _, Root) ->
  Root;
db_create_a([W|Ws], Allow, Width, Tmproot) ->
  S = p_sufdd(W),
  T = p_w_miss_a(S, Allow, Width),
  db_create_a(Ws, Allow, Width, p_id_union(Tmproot, T)).


multisufdd(N) when N =< 1 ->
  1;
multisufdd(M) ->
  N = subwordize(M),
  Object = ets:lookup(cache, {sufdd, N}),
  case Object of
    [{_, Result}] ->
      Result;
    _ ->
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      R1 = multisufdd(N1),
      R0 = multisufdd(N0),
      R = subword_union(R1, subword_union(store({X, N1, 1}), R0)),
      ets:insert(cache, {{sufdd, N}, R}),
      R
  end.


subwordize(N) when N=< 1 ->
  1;
subwordize(N) ->
  Object = ets:lookup(cache, {subwordize, N}),
  case Object of
    [{_, Result}] ->
      Result;
    _ ->
      [{_, {X, N1, N0}}] = ets:lookup(nodememory, N),
      R = store({X, subwordize(N1), subwordize(N0)}),
      ets:insert(cache, {{subwordize, N}, R}),
      R
  end.

elderflag0(N) when N =< 1 ->
  false;
elderflag0(N) ->
  Object = ets:lookup(order, N),
  case Object of
    [{_, false}] ->
      true;
    [{_, true}] ->
      ets:insert(order, {N, false});
    _ ->
      ets:insert(order, {N, false}),
      [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
      elderflag1(N1),
      elderflag0(N0)
  end.

elderflag1(N) when N =< 1 ->
  false;
elderflag1(N) ->
  Object = ets:lookup(order, N),
  case Object of
    [{_, _}] ->
      true;
    _ ->
      ets:insert(order, {N, true}),
      [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
      elderflag1(N1),
      elderflag0(N0)
  end.

mulsufdd(M) ->
  ets:new(order, [private, named_table]),
  N = subwordize(M),
  elderflag1(N),
  ets:insert(order, {sufdd, 0}),
  gensufdd(N),
  [{_, R}] = ets:lookup(order, sufdd),
  ets:delete(order),
  R.

gensufdd(N) when N =< 1 ->
  ok;
gensufdd(N) ->
  Object = ets:lookup(order, {gensufdd, N}),
  case Object of
    [{_, _}] ->
      ok;
    _ ->
      [{_, {_, N1, N0}}] = ets:lookup(nodememory, N),
      gensufdd(N1),
      gensufdd(N0),
      ets:insert(order, {{gensufdd, N}, ok}),
      [{_, Flag}] = ets:lookup(order, N),
      if
        Flag ->
          [{_, R}] = ets:lookup(order, sufdd),
          S = subword_union(N, R),
          ets:insert(order, {sufdd, S});
        true ->
          ok
      end
  end.




