
/**
  * @file jupyter.yap
  *
  * @brief JUpyter support.
  */

%:- yap_flag(gc_trace,verbose).
   :- module( jupyter,
               [jupyter_query/3,
 	       jupyter_query/4,
%% 	        op(100,fy,('$')),
%% 	   op(950,fy,:=),
%% 	   op(950,yfx,:=),
%% %	   op(950,fx,<-),
%% %	   op(950,yfx,<-),
%% 	   op(50, yf, []),
%% 	   op(50, yf, '()'),
%% 	   op(100, xfy, '.'),
%% 	   op(100, fy, '.'),
%%                blank/1,
	       streams/1
           ]
           ).

:-	 use_module(library(lists)).
:-	 use_module(library(maplist)).

:- use_module(library(hacks)).

:- reexport(library(complete)).
:- reexport(library(verify)).





:- python_import(sys).

%:- meta_predicate jupyter_query(+,:,+,-), jupyter_query(+,:,+).
	   
jupyter_query(Caller, Cell, Line, Bindings ) :-
	jupyter_cell(Caller, Cell, Line, Bindings).

jupyter_query(Caller, Cell, Line ) :-
    jupyter_query( Caller, Cell, Line, _Bindings ).

next_streams( _Caller, exit, _Bindings ) :-
%    Caller.answer := Bindings,
    !.
next_streams( _Caller, answer, _Bindings ) :-
%    Caller.answer := Bindings,
    !.
next_streams(_, redo, _ ) :-
    !.
next_streams( _, _, _ ). % :-
   % streams(false).

    

jupyter_cell(_Caller, Cell, _Line, _) :-
    jupyter_consult(Cell),	%stack_dump,
	fail.
jupyter_cell( _Caller, _, '', _) :- !.
jupyter_cell( _Caller, _, Line , _) :-
	blank( Line ),
	!.
jupyter_cell(Caller, _, Line, Bindings ) :-
    Query = Caller,
    catch(
	(python_query(Query, Goal, Port, Bindings),
	 Caller.q.port := Port,
	Caller.q.answer := Bindings),
	error(A,B),
	 system_error(A,B)
    ).

restreams(call) :-
    streams(true).
restreams(fail) :-
    streams(false).
restreams(answer).
restreams(exit) :-
    streams(false).
restreams(!).
restreams(external_exception(_)).
restreams(exception).

%:- meta_predicate

jupyter_consult(Text) :-
	blank( Text ),
	!.
jupyter_consult(Cell) :-
%	Name = 'Inp',
%	stream_property(Stream, file_name(Name) ),
%	setup_call_cleanup(
    catch(
	(
	    Options = [],
	    open_mem_read_stream( Cell, Stream),
	    load_files(user:Stream,[stream(Stream)| Options])
	),
	error(A,B),
  system_error(A,B)
    ).

blank(Text) :-
    atom(Text),
    !,
	atom_codes(Text, L),
	maplist( code_type(space), L).
blank(Text) :-
    string(Text),
    !,
    string_codes(Text, L),
    maplist( code_type(space), L).


streams(false) :-
   close(user_input),
    close(user_output),
    close(user_error).
streams( true) :-
    open('/python/input', read, _Input, [alias(user_input),bom(false),script(false)]),
    open('/python/sys.stdout', append, _Output, [alias(user_output)]),
    open('/python/sys.stderr', append, _Error, [alias(user_error)]).


:- if(  current_prolog_flag(apple, true) ).

:- putenv( 'LC_ALL', 'en_us:UTF-8').

plot_inline :-
	X := self.inline_plotting,
	nb_setval(inline, X ),
	X = true,
	!,
	:= (
	   import( matplotlib ),
	   matplotlib.use( `nbagg` )
	   ).

:- endif.

%:- ( start_low_level_trace ).
