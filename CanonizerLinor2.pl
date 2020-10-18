:- module(canonizer,[canonizing_set/2,canonizing_set/3,instance_specific_canonizing_set/3,instance_specific_canonizing_set/4,rest/3,validate/2,count_lexordered/2,count/2]).
:- nb_setval(bee_useXorClauses,false).
:- nb_setval(satSolver_module,glucose4).
:- use_module(bee('beeCompiler.lib/auxs.Mike/auxAdjacencyMatrix.pl'),[]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/isomorphism.pl'),[isomorphic/4, isomorphic_under_partition/5]).
:- use_module(bee('bApplications/auxs/auxRunExprCEGAR.pl'),[runExprCegar/6]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/lex_permutations.pl'),[lex_permutations/3,matrix_upper_triangle/2,simplify_lex/2]).
:- use_module(bee('beeCompiler.lib/auxs.Avi/graphSearch.pl'),[]).




count(3,4).
count(4,11).
count(5,34).
count(6,156).
count(7,1044).
count(8,12346).
count(9,274668).


debug(true).

count_lexordered(H,NSols) :-
    length(H,N),
    auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G),
    isomorphic(G,H,_,Cs-[]),
    graphSearch:count_graphs(N,NSols,[adjmatrix(G),constraints(Cs),sb(lexstar)]).
    
    

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
    
    
    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% given number of vertices N returns a canonizing set
% for general graphs with n vertices
% usage example: 
% ?- canonizing_set(8,CanSet).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
canonizing_set(N,CanSet):-
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,AdjMatrix),
	%loop_for_ten(1,AdjMatrix,Cs-[]),
	solveCegar(can(AdjMatrix,[]),CanSet).
loop_for_ten(I,_,Cs-[]):- I>=11,!.
loop_for_ten(I,AdjMatrix,Cs):-writeln(I),
I<11,!,
encodeInit1(can(G1,CsInit),Map,Cs1-Cs2),writeln(Cs1),
I1 is I+1,
loop_for_ten(I1,AdjMatrix,Cs2),
append(Cs1,Cs2,Cs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% same as the predicate above but enables to initialize
% the canonizing set
% usage example: 
% ?- canonizing_set(4,[[2,1,3,4],[1,3,2,4]],CanSet).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%	
	
canonizing_set(N,InitialPs,CanSet):-
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,AdjMatrix),
	lex_permutations(AdjMatrix,InitialPs,Cs-[]),
	solveCegar(can(AdjMatrix,Cs),CanSet).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% given an adjacency matrix and a set of constraints on it, returns
% a canonizing set for the specific instance
% usually should be used as following: 
% ?- encode(Instance,map(AdjMatrix),Cs), instance_specific_canonizing_set(AdjMatrix,Cs,CanSet).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
instance_specific_canonizing_set(AdjMatrix,Cs,CanSet):-
	solveCegar(can(AdjMatrix,Cs),CanSet).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% degree sequences need to be handled in a different way since they impose a restriction on the 
% isomorphism. (it will be more elegant if the predicate will get a partition rather than degree
% sequence)    
% ?- encode(Instance,map(AdjMatrix),Cs), instance_specific_canonizing_set(AdjMatrix,Cs,Ds,CanSet).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
	
instance_specific_canonizing_set(AdjMatrix,Cs,Degrees,CanSet):-
	solveCegar(can(AdjMatrix,Cs,Degrees),CanSet).
	

solveCegar(Instance,Sol):-	
	runExprCegar(Instance,Sol,
		canonizer:encodeInit1,
		canonizer:encodeS,
		canonizer:decodeS,
		canonizer:decodeF).


encodeInit1(can(G1,CsInit),Map,Cs):-
	length(G1,N),
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G2),
	isomorphic(G1,G2,F,Cs1-Cs2),
	matrix_upper_triangle(G1,Str1),
	matrix_upper_triangle(G2,Str2),
	simplify_lex(lex(Str2,Str1),lex(Str2a,Str1a)),
	length(Str1,N2),
	MidPlus is floor((N2/2))+1,writeln(MidPlus),
	MidMinus is floor((N2/2))-1,writeln(MidMinus),
	Cs2 = [bool_array_sum_leq(Str1,MidPlus),bool_array_sum_geq(Str1,MidMinus),bool_arrays_lexLt(Str2a,Str1a)],
	Map = map((G1,F),[]),
	append(CsInit,Cs1,Cs).
	
encodeInit(can(G1,CsInit),Map,Cs):-
	length(G1,N),
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G2),
	isomorphic(G1,G2,F,Cs1-Cs2),
	matrix_upper_triangle(G1,Str1),
	matrix_upper_triangle(G2,Str2),
	simplify_lex(lex(Str2,Str1),lex(Str2a,Str1a)),
	Cs2 = [bool_arrays_lexLt(Str2a,Str1a)],
	Map = map((G1,F),[]),
	append(CsInit,Cs1,Cs).	
encodeInit(can(G1,CsInit,Ds),Map,Cs):-
	length(G1,N),
	auxAdjacencyMatrix:createAdjacencyMatrix(N,-1,G2),
	get_orbits(Ds,Part),
	isomorphic_under_partition(G1,G2,Part,F,Cs1-Cs2),
	matrix_upper_triangle(G1,Str1),
	matrix_upper_triangle(G2,Str2),
	simplify_lex(lex(Str2,Str1),lex(Str2a,Str1a)),
	Cs2 = [bool_arrays_lexLt(Str2a,Str1a)],
	Map = map((G1,F),[]),
	append(CsInit,Cs1,Cs).
	
encodeS(can(G1,_),PrevMap,F0,NewMap,Cs):-
	PrevMap = map((G1,F),PrevSols),
	NewMap= map((G1,F),[F0|PrevSols]),
	lex_permutations(G1,[F0],Cs-[]).

encodeS(can(G1,_,_),PrevMap,F0,NewMap,Cs):-
	PrevMap = map((G1,F),PrevSols),
	NewMap= map((G1,F),[F0|PrevSols]),
	lex_permutations(G1,[F0],Cs-[]).
	
	
decodeS(map((_,F),_),Perm):-
	bDecode:decodeIntArray(F,Perm).
	
	
decodeF(_, Map,FSolution):-
    Map = map(_, PrevSols),
    FSolution = PrevSols.
    
    	
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
