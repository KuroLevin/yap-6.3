pl_graphs(Dir - Mod) :-
      atom( Dir ),
	format(' ************* GRAPH: ~a ***********************/~n', [Dir]),
	atom_concat([Dir,'/*'], Pattern), % */
	expand_file_name( Pattern, Files ),
	member( File, Files ),
	( ( sub_atom(File,_,_,0,'.yap') ; sub_atom(File,_,_,0,'.pl') ) ->
	  build_graph( File , Mod )
	;
	  exists_directory( File ),
	  \+ atom_concat(_, '/.', File),
	  \+ atom_concat(_, '/..', File),
	  \+ atom_concat(_, '/.git', File),
	  pl_graphs( File - Mod )
	),
	fail.
pl_graphs(_).

%%
% pl_graph( File, Mod)
% adds a node to the file graph and marks which files are modules
%
% main side-effect facts like edge( F0-Mod:File )
%                             exported( F-M , N/A ) or exported(F- M. Op ),
%                             module_on ( M, File )
%                             pred ( M :N/A )
%
build_graph(F, Mod) :-
                                %    writeln(F),
	preprocess_file( F, PF ),
	catch( open(PF, read, S, [scripting(true)]), _, fail ),
	repeat,
	nb_getval( current_module, MR ),
	catch(read_term( S, T, [term_position(Pos),module(MR),comments(Cs)] ), Throw, (writeln(Throw))),
	(
	 T == end_of_file
	->
	 !,% also, clo ops defined in the module M, if M \= Mod
	% ( sub_atom(F,_,_,_,'/matrix.yap') ->  start_low_level_trace ; nospyall ),
	 close(S)
	;
	 stream_position_data( line_count, Pos, Line ),
	 maplist( comment, Cs ),
	 nb_setval( line, Line ),
	 nb_getval( current_module, MC0 ),
	 ( Mod == prolog -> MC = prolog ; MC = MC0 ),
	 get_graph( T, F, Pos, MC  ),
	 fail
	).


get_graph( V , _F, _Pos, _M ) :-
	var( V ),
	!,
	error( instantiation_error ).
get_graph( T, _F, _Pos, _M0 ) :-
	var(T),
	!.
get_graph( M:T, F, _Pos, _M0 ) :- !,
	get_graph( T, F, _Pos, M ).
get_graph( ( M:H :- B), F, _Pos, M0 ) :-
	!,
	get_graph( (H :- M0:B), F, _Pos, M ).
get_graph( ( M:H --> B), F, _Pos, M0 ) :-
	!,
	get_graph( ( H --> M0:B), F, _Pos, M ).
get_graph( ( A, _ --> B), F, _Pos, M ) :-
	get_graph( ( A --> B), F, _Pos, M ).
get_graph( (H --> B), F, _Pos, M ) :-
	!,
	functor( H, N, Ar),
	Ar2 is Ar+2,
	add_deps( B, M, M:N/Ar2, F, _Pos, 2 ).
get_graph( (H :- B), F, _Pos, M ) :-
	!,
	functor( H, N, Ar),
	add_deps( B, M, M:N/Ar, F, _Pos, 0 ).
%% switches to new file n
get_graph( (:-include( Fs ) ), F, _Pos, M ) :-
	!,
	source_graphs( M, F, Fs ).
get_graph( (?- _ ), _F, _Pos, _M ) :- !.
get_graph( (:- _ ), _F, _Pos, _M ) :- !.

source_graphs( M, F, Fs ) :-
	maplist( source_graph( M, F ), Fs ), !.
source_graphs( M, F, Fs ) :-
	search_file( Fs, F, pl, NF ),
	build_graph( NF , M ), !.

add_deps(V, _M, _P, _F, _Pos, _) :-
	var(V), !.
add_deps(M1:G, _M, _P, _F, _Pos,L) :-
	!,
	always_strip_module(M1:G, M2, G2),
	add_deps(G2, M2, _P, _F, _Pos, L).
add_deps((A,B), M, P, F, _Pos, L) :-
	!,
	add_deps(A, M, P, F, _Pos, L),
	add_deps(B, M, P, F, _Pos, L).
add_deps((A;B), M, P, F, _Pos, L) :- !,
	add_deps(A, M, P, F, _Pos, L),
	add_deps(B, M, P, F, _Pos, L).
add_deps((A|B), M, P, F, _Pos, L) :- !,
	add_deps(A, M, P, F, _Pos, L),
	add_deps(B, M, P, F, _Pos, L).
add_deps((A->B), M, P, F, _Pos, L) :- !,
	add_deps(A, M, P, F, _Pos, L),
	add_deps(B, M, P, F, _Pos, L).
add_deps((A*->B), M, P, F, _Pos, L) :- !,
	add_deps(A, M, P, F, _Pos, L),
	add_deps(B, M, P, F, _Pos, L).
add_deps(once(A), M, P, F, _Pos, L) :- !,
	add_deps(A, M, P, F, _Pos, L).
add_deps({A}, M, P, F, _Pos, 2) :- !,
	add_deps(A, M, P, F, _Pos, 0).
add_deps([_|_], M, P, F, Pos, 2) :-
	!,
	put_dep( (F-M:P :- prolog:'C'/3 ), Pos ).
add_deps(String, _M, _P, _F, _Pos, _) :-  string(String), !.
add_deps([], _M, _P, _F, _Pos, 2) :- !.
add_deps(!, _M, _P, _F, _Pos, _) :- !.
add_deps(true, _M, _P, _F, _Pos, 0) :- !.
add_deps(false, _M, _P, _F, _Pos, 0) :- !.
add_deps(fail, _M, _P, _F, _Pos, 0) :- !.
add_deps(repeat, _M, _P, _F, _Pos, 0) :- !.
add_deps(A, M, P, F, Pos, L) :-
                                % we're home, M:N/Ar -> P=M1:N1/A1
	functor(A, N, Ar0),
	Ar is Ar0+L,
	put_dep( ( F-M:P :- F-M:N/Ar ), Pos ).

put_dep( (Target :- F0-M:Goal ), Pos ) :-
exported( ( F0-M:Goal :- F1-M1:N/Ar ) ), !,
                                %follow ancestor chain
ancestor( ( F1-M1:N/Ar :- FA-MA:NA/Ar )  ),
put_dep( ( Target :- FA-MA:NA/Ar ), Pos  ).
                                % the base case, copying from the same module ( but maybe not same file 0.
put_dep( ( Target :- _F-M:N/Ar ) , _ ) :-
m_exists(M:N/Ar, F0),
!,
assert_new( edge( ( Target :- F0-M:N/Ar ) ) ).
                                % prolog is visible ( but maybe not same file ).
put_dep( ( Target :- _F-_prolog:N/Ar ), _ ) :-
m_exists(prolog:N/Ar, F0),
!,
assert_new( edge( ( Target :- F0-prolog:N/Ar ) ) ).
put_dep( ( _Target :- _F-Mod:_N/_Ar ), _Pos) :-
var( Mod ), !.
put_dep( ( Target :- F-Mod:N/Ar ), Pos) :-
atom( Mod ),
stream_position_data( line_count, Pos, Line ),
assert_new( undef( (Target :- F-Mod:N/Ar ), Line) ).

ancestor( ( Younger :- Older) ) :-
exported(  ( Mid :- Older ) ), !,
ancestor( ( Younger :- Mid) ).
ancestor( (Older :- Older) ).

m_exists(P, F) :- private( F, P ), !.
m_exists(P, F) :- public( F, P ).
