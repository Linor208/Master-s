:- module(canonizer4Linor,[canonizing_set/2, canonizing_set/3]).
:- nb_setval(bee_useXorClauses,false).
:- nb_setval(satSolver_module,glucose4).
:- use_module(bee('beeCompiler.lib/auxs.Mike/auxAdjacencyMatrix.pl'),[]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/isomorphism.pl'),[isomorphic/4, isomorphic_under_partition/5]).
:- use_module(bee('bApplications/auxs/auxRunExprCEGAR.pl'),[runExprCegar/6]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/lex_permutations.pl'),[lex_permutations/3,matrix_upper_triangle/2,simplify_lex/2]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/reducer.pl'),[]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/canonizer.pl'),[]).

:- use_module(bee('beeCompiler.lib/auxs.Avi/graphSearch.pl'),[]).

% :- use_module(bee('beeCompiler.lib/clasp/clasp'),[]). % fast solution enumeration

% catalog of canonical graphs
:- use_module(catalog, []).

count(3,4).
count(4,11).
count(5,34).
count(6,156).
count(7,1044).
count(8,12346).
count(9,274668).


debug(false).

validate(N,CanSet) :-
    auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,AdjMatrix),
    lex_permutations:lex_permutations(AdjMatrix,CanSet,Cs-[]),
    writeln('*************************TEST CAN. SET ********************************'),
    graphSearch:count_graphs(N,Cnt,[adj(AdjMatrix),constraints(Cs)]),
    writeln('*********************************************************'),
    count(N,Cnt).

% computes a delta that required to make the given set of permutations a complete 
% symmetry breaking constraint
rest(N, GivenPermutations, Delta) :-
    auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,AdjMatrix),
    lex_permutations:lex_permutations(AdjMatrix,GivenPermutations,Cs-[]),
    canonizer:instance_specific_canonizing_set(AdjMatrix,Cs,Delta),
    append(GivenPermutations,Delta,CanSet),
    %DEBUG
    (debug(true) -> validate(N,CanSet) ; true).


test(N,CanSets) :-
    canonizing_set_per_isomorphism_class(N,CanSets),
    %sort_by_size(CanSets,Sorted_CanSets),
    printSet(CanSets).
    %sort_by_edges(CanSets,SortedCanSets).
    
canonizing_set_per_isomorphism_class(N,CanSets) :-
    count(N,Max),
    canonizing_set_per_isomorphism_class(N,CanSets,1,Max).
    
canonizing_set_per_isomorphism_class(N,[(stats(g(I), edges(NEdges), adj(H), pi(Size),reduce_pi(SizeReducedCanSetH), pi_rest(SizeDelta), all_reduced(SizeReduced),can_set(CanSetH)))|CanSets],I,J) :-
    I =< J,!,
    catalog:graph(N,I,H),
    (canonizing_set(N,CanSetH,[isomorphism_class(H)]) ->
	true
	;
	CanSetH = []
    ),
    I1 is I+1,!,
    length(CanSetH,Size),
%     length(CanSetHReduced,SizeReduced),
    rest(N, CanSetH, Delta),
    reducer:reduce(CanSetH,ReduceCanSetH),
    length(ReduceCanSetH,SizeReducedCanSetH),
    append(CanSetH,Delta,GlobalCanSet),
    reducer:reduce(GlobalCanSet,ReducedGlobalCanSet),
    length(ReducedGlobalCanSet,SizeReduced),
    length(Delta,SizeDelta),
    lex_permutations:matrix_upper_triangle(H,UpperTriangle),
    count_ones(UpperTriangle,NEdges),
    %writeln('------------------------------------------'),    
    %writeln((g(I), edges(NEdges), adj(H), pi(Size), pi_rest(SizeDelta))),
    %writeln('------------------------------------------'),
    canonizing_set_per_isomorphism_class(N,CanSets,I1,J). 

canonizing_set_per_isomorphism_class(_,[],I,J) :-
    I > J.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% given number of vertices N returns a canonizing set
% for general graphs with n vertices
% usage example: 
% ?- canonizing_set(8,CanSet).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
canonizing_set(N,CanSet) :-
    canonizing_set(N,CanSet,[]).

canonizing_set(N,CanSet,Options):-
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G1),
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G2),
	solveCegar(canPair(G1,G2,Options),CanSet).


solveCegar(Instance,Sol):-	
	runExprCegar(Instance,Sol,
		canonizer4Linor:encodeInit,
		canonizer4Linor:encodeS,
		canonizer4Linor:decodeS,
		canonizer4Linor:decodeF).

% TODO: select a permutation from F1,F2	
rank(F1,_F2, F, _Options) :- 
    %option(isomorphism_class(H),Options, []),
    F = F1. % for now select the first permutation by default


encodeInit(canPair(G1,G3,Options),Map,Cs):-
	length(G1,N),
	% first permutation
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G2),
	isomorphic(G1,G2,F1,Cs1-Cs2),
	matrix_upper_triangle(G1,Str1),
	matrix_upper_triangle(G2,Str2),
	simplify_lex(lex(Str2,Str1),lex(Str2a,Str1a)),
	Cs2 = [bool_arrays_lexLt(Str2a,Str1a)|Cs3],
	% second permutation
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G4),
	isomorphic(G3,G4,F2,Cs3-Cs4),
	matrix_upper_triangle(G3,Str3),
	matrix_upper_triangle(G4,Str4),
	simplify_lex(lex(Str4,Str3),lex(Str4a,Str3a)),
	Cs4 = [bool_arrays_lexLt(Str4a,Str3a)|Cs5],
	%
	option(isomorphism_class(H),Options,unspecified),
	ground(H),
	( H \= unspecified ->
	    isomorphic(G1,H,_,Cs5-[])
	    ;
	    Cs5 = []
	),
	Map = map(p1(G1,F1),p2(G3,F2),[]),
	Cs = Cs1.	
		
		
encodeS(canPair(G1,G3,Options),PrevMap,(F1Dec,F2Dec),NewMap,Cs):-
	PrevMap = map(p1(G1,F1),p2(G3,F2), PrevSols),
	% choose one permutation out of two (F1Dec, F2Dec)
	rank(F1Dec,F2Dec,BestPermutation,Options),
	NewMap= map(p1(G1,F1),p2(G3,F2), [BestPermutation|PrevSols]),
	lex_permutations(G1,[BestPermutation],Cs-[]).
	
decodeS(map(p1(_,F1),p2(_,F2),_),(Perm1,Perm2)):-
	bDecode:decodeIntArray(F1,Perm1),
	bDecode:decodeIntArray(F2,Perm2).
	
decodeF(_, Map,FSolution):-
    Map = map(_, _, PrevSols),
    FSolution = PrevSols.
    
    
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Auxs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
    

%sort_by_edges(List1,List2):-writeln("here"),
    %List1=[(stats(_,edges(NEdges),_,_,_,_,_),_)|Rest],writeln("here2"),
    %sort_by_edges_aux(Rest,[List1|List2],[],NEdges).
    
%sort_by_edges_aux([],Acc,Acc,_):-!.
%sort_by_edges_aux([(Stats,Set)|Rest],[L2|Rest3],[Stats1|Rest2],MinEdge):-writeln("here3"),
    %Stats=(stats(_, edges(NEdges), _, _,_,_,_)),
    %(NEdges =< MinEdge->writeln(NEdges),write(" "),writeln(MinEdge),
        %MinEdge=NEdges,writeln("here4"),
        %L2=[(Stats,Set),L2|Rest3];
        %edges_aux(Stats,[Stats1|Rest2],List2),
        %L2=List2),
        %sort_by_edges_aux(Rest,Rest2,MinEdge).
        
        
        
quick_sort2(List,Sorted):-q_sort(List,[],Sorted).
q_sort([],Acc,Acc).
q_sort([H|T],Acc,Sorted):-
	pivoting(H,T,L1,L2),
	q_sort(L1,Acc,Sorted1),q_sort(L2,[H|Sorted1],Sorted).
	
pivoting(H,[],[],[]).
pivoting(H,[X|T],[X|L],G):-
    H=(stats(_, edges(NEdges), _, _,_,_,_,_)),
    X=(stats(_, edges(NEdges1), _, _,_,_,_,_)),
    NEdges1=<NEdges,
    pivoting(H,T,L,G).

pivoting(H,[X|T],L,[X|G]):-
    H=(stats(_, edges(NEdges), _, _,_,_,_,_)),
    X=(stats(_, edges(NEdges1), _, _,_,_,_,_)),
    NEdges1>NEdges,
    pivoting(H,T,L,G).



printSet([]):-!.
printSet([Stats|Sets]):-
    writeln('------------------------------------------'),    
    writeln(Stats),
    writeln('------------------------------------------'),
    printSet(Sets).
    
    
writeToLatex([]):-!.
writeToLatex([Set|Rest]):-
    Set=(stats(g(I), edges(NEdges), adj(H), pi(Size),reduce_pi(SizeReducedCanSetH), pi_rest(SizeDelta), all_reduced(SizeReduced),_)),
    write(I),write('&'), write(NEdges), write('&'),write(Size),write('&'), write(SizeReducedCanSetH), write('&'),write(SizeDelta),
    write('&'),write(SizeReduced),write('\\\\'),write('\\hline'),write(' '),
    writeToLatex(Rest).
