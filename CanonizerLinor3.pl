:-module(linorCanonizer, []).

:- nb_setval(bee_useXorClauses,false).
:- nb_setval(satSolver_module,glucose4).
:- use_module(bee('beeCompiler.lib/auxs.Mike/auxAdjacencyMatrix.pl'),[]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/isomorphism.pl'),[isomorphic/4, isomorphic_under_partition/5]).
:- use_module(bee('bApplications/auxs/auxRunExprCEGAR.pl'),[runExprCegar/6]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/lex_permutations.pl'),[lex_permutations/3,matrix_upper_triangle/2,simplify_lex/2]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/graphSearch.pl'),[]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/canonizer.pl'),[]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/reducer.pl'),[]).




count(3,4).
count(4,11).
count(5,34).
count(6,156).
count(7,1044).
count(8,12346).
count(9,274668).


debug(true).

compute_canonizing_set_with_reduced(N):-
        StartCan is cputime,
        canonizing_set(N,CanSet, [restrictEdges(true)]),
        CanTime is cputime-StartCan,
        StartRest is cputime,
        rest(N,CanSet,Delta),
        RestTime is cputime-StartRest,
        length(CanSet,CanSetLen),
        length(Delta,DeltaSize),
        %append('Results_For_eleven_NoReduce.csv'),
        %write(CanTime),write(','),write(CanSetLen),write(','),write(CanSet),write(','),write(DeltaSize),writeln(' '),
        %told,
        StartRed is cputime,
        append(CanSet,Delta,AllPermutations),
        reducer:reduce(AllPermutations,ReduceCanSet),
        RedTime is cputime-StartRed,
        length(CanSet,CanSetLen),
        length(ReduceCanSet,RedCanSetLen),
        append('resultsFor10_WithDegs.csv'),
        write("25-26"),write(','), write(CanTime),write(','),write(CanSetLen),write(','), write(RestTime),write(','),write(RedTime),write(','),write(RedCanSetLen),write(','),write(DeltaSize),writeln(' '),
        told,
        writeln(can_time(CanTime)),writeln(can_size(CanSetLen)),writeln(rest(DeltaSize)),writeln(red_time(RedTime)),writeln(red_size(RedCanSetLen)).
        


count_lexordered(H,NSols) :-
    length(H,N),
    auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G),
    isomorphic(G,H,_,Cs-[]),
    graphSearch:count_graphs(N,NSols,[adjmatrix(G),constraints(Cs),sb(lexstar)]).
    
    

validate(N,CanSet) :-
    auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,AdjMatrix),
    lex_permutations:lex_permutations(AdjMatrix,CanSet,Cs-[]),
    writeln('*************************TEST CAN. SET ********************************'),
    graphSearch:count_graphs(N,Cnt,[adj(AdjMatrix),constraints(Cs)]),writeln(Cnt),
    writeln('*********************************************************').

% computes a delta that required to make the given set of permutations a complete 
% symmetry breaking constraint
rest(N, GivenPermutations, Delta) :-
    auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,AdjMatrix),
    lex_permutations:lex_permutations(AdjMatrix,GivenPermutations,Cs-[]),
    (canonizer:instance_specific_canonizing_set(AdjMatrix,Cs,Delta1) -> 
        Delta = Delta1
        ;
        Delta = []
    ),!,
    append(GivenPermutations,Delta,CanSet).
    %DEBUG
    %(debug(true) -> validate(N,CanSet) ; true).
    
    
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% given number of vertices N returns a canonizing set
% for general graphs with n vertices
% usage example: 
% ?- canonizing_set(8,CanSet).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
canonizing_set(N,CanSet, Options):-
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,AdjMatrix),
	%loop_for_ten(1,AdjMatrix,Cs-[]),
	solveCegar(can(AdjMatrix,[], Options),CanSet).
/*	
loop_for_ten(I,_,Cs-[]):- I>=11,!.
loop_for_ten(I,AdjMatrix,Cs):-writeln(I),
I<11,!,
encodeInit1(can(G1,CsInit),Map,Cs1-Cs2),writeln(Cs1),
I1 is I+1,
loop_for_ten(I1,AdjMatrix,Cs2),
append(Cs1,Cs2,Cs).*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% same as the predicate above but enables to initialize
% the canonizing set
% usage example: 
% ?- canonizing_set(4,[[2,1,3,4],[1,3,2,4]],CanSet).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
	
canonizing_set(N,InitialPs,CanSet,Options):-
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,AdjMatrix),
	lex_permutations(AdjMatrix,InitialPs,Cs-[]),
	solveCegar(can(AdjMatrix,Cs,Options),CanSet).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% given an adjacency matrix and a set of constraints on it, returns
% a canonizing set for the specific instance
% usually should be used as following: 
% ?- encode(Instance,map(AdjMatrix),Cs), instance_specific_canonizing_set(AdjMatrix,Cs,CanSet).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
instance_specific_canonizing_set(AdjMatrix,Cs,CanSet,Options):-
	solveCegar(can(AdjMatrix,Cs,Options),CanSet).
	

solveCegar(Instance,Sol):-	
	runExprCegar(Instance,Sol,
		linorCanonizer:encodeInit,
		linorCanonizer:encodeS,
		linorCanonizer:decodeS,
		linorCanonizer:decodeF).


encodeInit(can(G1,CsInit,Options),Map,Cs):-
	length(G1,N),
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G2),
	isomorphic(G1,G2,F,Cs1-Cs2),
	matrix_upper_triangle(G1,Str1),
	matrix_upper_triangle(G2,Str2),
	simplify_lex(lex(Str2,Str1),lex(Str2a,Str1a)),
	length(Str1,N2),
	option(restrictEdges(X),Options,false),
	(X = true -> 
        writeln('WARNING: edge size is restricted!'),
        MidPlus is floor((N2/2))+1,
        MidMinus is floor((N2/2))-1,
        Cs2 = [bool_array_sum_leq(Str1,MidPlus),bool_array_sum_geq(Str1,MidMinus)|Cs3]
        ;
        writeln('NO RESTRICTION!'),
        Cs = Cs3
    ),
    encodeDeg(N,G1,Cs4),
    Cs3 = [bool_arrays_lexLt(Str2a,Str1a)|Cs4],
	Map = map((G1,F),[]),
	append(CsInit,Cs1,Cs).
	
	
encodeS(can(G1,_,_),PrevMap,F0,NewMap,Cs):-
	PrevMap = map((G1,F),PrevSols),
	NewMap= map((G1,F),[F0|PrevSols]),
	lex_permutations(G1,[F0],Cs-[]).

	
decodeS(map((_G,F),_),Perm):-
	bDecode:decodeIntArray(F,Perm).
    %matrix_upper_triangle(G,Str1),
    %count_ones(Str1,GOnes),
    %append('DistributedGraphsOn7_1.csv'),
    %write(GOnes),writeln('  '),
    %told.
	
	
decodeF(_, Map,FSolution):-
    Map = map(_, PrevSols),
    FSolution = PrevSols.
    
 encodeDeg(N,AdjMatrix,Cs):-
    sum_rows(N,AdjMatrix,As,Cs-Cs1),
    createXs(N,As,Xs,Cs1-Cs2),
    flatten2(Xs,Xs1),
    N1 is N+25,
    N2 is N+26,
    Cs2=[bool_array_sum_leq(Xs1,N2),bool_array_sum_geq(Xs1,N1)].
    
sum_rows(_,[],[],Cs-Cs):-!.    
sum_rows(N,[RowI|Rows],[Ai|As], Cs-Cs2):-
    Cs=[new_int(Ai,0,N),bool_array_sum_eq(RowI,Ai)|Cs1],
    sum_rows(N,Rows,As,Cs1-Cs2).
    
createXs(_,[],[],Cs-Cs):-!.    
createXs(N,[Ai|As],[Xij|Xs],Cs-Cs2):-
    createXs_aux(N,Ai,As,Xij,Cs-Cs1),
    createXs(N,As,Xs,Cs1-Cs2).

createXs_aux(_,_,[],[],Cs-Cs):-!.    
createXs_aux(N,Ai,[Aj|As],[Xij|Xs],Cs-Cs2):-
    
    Cs=[int_neq_reif(Ai,Aj,Xij)|Cs1],
    createXs_aux(N,Ai,As,Xs,Cs1-Cs2).
get_orbits(Ds,Orbits):-
	get_orbits(Ds,1,[],Orbits).
	
get_orbits([],_,O,[O]).	
get_orbits([_],I,O,[[I|O]]).

get_orbits([X,X|Ds],I,O,Orbits):-
	I1 is I+1,
	get_orbits([X|Ds],I1,[I|O],Orbits).
	
get_orbits([X,Y|Ds],I,O,[[I|O]|Orbits]):-
	X \= Y,
	I1 is I+1,
	get_orbits([Y|Ds],I1,[],Orbits).	
	
count_ones(List,Cnt) :-
    count_ones(List,0,Cnt).
    
count_ones([],Cnt,Cnt) :-!.
count_ones([X|Xs],Acc,Cnt) :-
    (1 is X ->
	Acc1 is Acc + 1
	;
	Acc1 is Acc
    ),!,
    count_ones(Xs,Acc1,Cnt).
flatten2( A, B):- flatten2( A, B, []).

flatten2( [], Z, Z):- !.                                     
flatten2([Atom|ListTail], [Atom|X], Z) :-                      
    \+is_list(Atom), !,                                       
    flatten2(ListTail,X,Z).                                 
flatten2([List|ListTail],X,Z) :-                             
    flatten2(List,X, Y),      
    flatten2(ListTail,Y,Z).          
