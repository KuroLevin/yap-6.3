#false
cat << "EOF" > tmp
/** @pred wam_profiler_show_ops_by_group(+ _A_) 


Display the current value for the counters, organized by groups, using
label  _A_. The label must be an atom.




 */
EOF
sed -e "872r tmp" /Users/vsc/git/yap-6.3/C/analyst.c > x
     mv x /Users/vsc/git/yap-6.3/C/analyst.c

#false
cat << "EOF" > tmp
/** @pred wam_profiler_show_op_counters(+ _A_) 


Display the current value for the counters, using label  _A_. The
label must be an atom.

 
*/
EOF
sed -e "863r tmp" /Users/vsc/git/yap-6.3/C/analyst.c > x
     mv x /Users/vsc/git/yap-6.3/C/analyst.c

#false
cat << "EOF" > tmp
/** @pred wam_profiler_reset_op_counters 


Reinitialize all counters.

 
*/
EOF
sed -e "855r tmp" /Users/vsc/git/yap-6.3/C/analyst.c > x
     mv x /Users/vsc/git/yap-6.3/C/analyst.c

#false
cat << "EOF" > tmp
/** @pred  static_array_location(+ _Name_, - _Ptr_) 


Give the location for  a static array with name
 _Name_.

 
*/
EOF
sed -e "2636r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  static_array_to_term(? _Name_, ? _Term_) 


Convert a static array with name
 _Name_ to a compound term of name  _Name_.

This built-in will silently fail if the there is no static array with
that name.

 
*/
EOF
sed -e "2635r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  close_static_array(+ _Name_) 


Close an existing static array of name  _Name_. The  _Name_ must
be an atom (named array). Space for the array will be recovered and
further accesses to the array will return an error. 

 
*/
EOF
sed -e "2630r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  reset_static_array(+ _Name_) 


Reset static array with name  _Name_ to its initial value.

 
*/
EOF
sed -e "2629r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  array_element(+ _Name_, + _Index_, ? _Element_) 


Unify  _Element_ with  _Name_[ _Index_]. It works for both
static and dynamic arrays, but it is read-only for static arrays, while
it can be used to unify with an element of a dynamic array.

 
*/
EOF
sed -e "2628r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  add_to_array_element(+ _Name_, + _Index_, + _Number_, ? _NewValue_)  


Add  _Number_  _Name_[ _Index_] and unify  _NewValue_ with
the incremented value. Observe that  _Name_[ _Index_] must be an
number. If  _Name_ is a static array the type of the array must be
`int` or `float`. If the type of the array is `int` you
only may add integers, if it is `float` you may add integers or
floats. If  _Name_ corresponds to a dynamic array the array element
must have been previously bound to a number and `Number` can be
any kind of number.

The `add_to_array_element/3` built-in actually uses
`setarg/3` to update elements of dynamic arrays. For intensive
operations we suggest it may be less expensive to unify each element
of the array with a mutable terms and to use the operations on mutable
terms.




 */
EOF
sed -e "2627r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  update_array(+ _Name_, + _Index_, ? _Value_)  


Attribute value  _Value_ to  _Name_[ _Index_]. Type
restrictions must be respected for static arrays. This operation is
available for dynamic arrays if `MULTI_ASSIGNMENT_VARIABLES` is
enabled (true by default). Backtracking undoes  _update_array/3_ for
dynamic arrays, but not for static arrays.

Note that update_array/3 actually uses `setarg/3` to update
elements of dynamic arrays, and `setarg/3` spends an extra cell for
every update. For intensive operations we suggest it may be less
expensive to unify each element of the array with a mutable terms and
to use the operations on mutable terms.

 
*/
EOF
sed -e "2625r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  mmapped_array(+ _Name_, + _Size_, + _Type_, + _File_) 


Similar to static_array/3, but the array is memory mapped to file
 _File_. This means that the array is initialized from the file, and
that any changes to the array will also be stored in the file. 

This built-in is only available in operating systems that support the
system call `mmap`. Moreover, mmapped arrays do not store generic
terms (type `term`).

 
*/
EOF
sed -e "2624r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  resize_static_array(+ _Name_, - _OldSize_, + _NewSize_) 


Expand or reduce a static array, The  _Size_ must evaluate to an
integer. The  _Name_ must be an atom (named array). The  _Type_
must be bound to one of `int`, `dbref`, `float` or
`atom`.

Note that if the array is a mmapped array the size of the mmapped file
will be actually adjusted to correspond to the size of the array.

 
*/
EOF
sed -e "2623r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  static_array(+ _Name_, + _Size_, + _Type_) 


Create a new static array with name  _Name_. Note that the  _Name_
must be an atom (named array). The  _Size_ must evaluate to an
integer.  The  _Type_ must be bound to one of types mentioned
previously.

 
*/
EOF
sed -e "2622r tmp" /Users/vsc/git/yap-6.3/C/arrays.c > x
     mv x /Users/vsc/git/yap-6.3/C/arrays.c

#false
cat << "EOF" > tmp
/** @pred  atomic_concat(+ _As_,? _A_) 


The predicate holds when the first argument is a list of atomic terms, and
the second unifies with the atom obtained by concatenating all the
atomic terms in the first list. The first argument thus may contain
atoms or numbers.

 
*/
EOF
sed -e "2335r tmp" /Users/vsc/git/yap-6.3/C/atomic.c > x
     mv x /Users/vsc/git/yap-6.3/C/atomic.c

#false
cat << "EOF" > tmp
/** @pred  atom_number(? _Atom_,? _Number_) 


The predicate holds when at least one of the arguments is ground
(otherwise, an error message will be displayed). If the argument
 _Atom_ is an atom,  _Number_ must be the number corresponding
to the characters in  _Atom_, otherwise the characters in
 _Atom_ must encode a number  _Number_.

 
*/
EOF
sed -e "2320r tmp" /Users/vsc/git/yap-6.3/C/atomic.c > x
     mv x /Users/vsc/git/yap-6.3/C/atomic.c

#false
cat << "EOF" > tmp
/** @pred  number_atom(? _I_,? _L_) 



The predicate holds when at least one of the arguments is ground
(otherwise, an error message will be displayed). The argument  _I_ must
be unifiable with a number, and the argument  _L_ must be unifiable
with an atom representing the number.

 
*/
EOF
sed -e "2306r tmp" /Users/vsc/git/yap-6.3/C/atomic.c > x
     mv x /Users/vsc/git/yap-6.3/C/atomic.c

#false
cat << "EOF" > tmp
/** @pred  number_chars(? _I_,? _L_) is iso 

The predicate holds when at least one of the arguments is ground
(otherwise, an error message will be displayed). The argument  _I_ must
be unifiable with a number, and the argument  _L_ with the list of the
characters of the external representation of  _I_.

 
*/
EOF
sed -e "2296r tmp" /Users/vsc/git/yap-6.3/C/atomic.c > x
     mv x /Users/vsc/git/yap-6.3/C/atomic.c

#false
cat << "EOF" > tmp
/** @pred  atom_length(+ _A_,? _I_) is iso 


The predicate holds when the first argument is an atom, and the second
unifies with the number of characters forming that atom.

 
*/
EOF
sed -e "2284r tmp" /Users/vsc/git/yap-6.3/C/atomic.c > x
     mv x /Users/vsc/git/yap-6.3/C/atomic.c

#false
cat << "EOF" > tmp
/** @pred  atom_chars(? _A_,? _L_) is iso 


The predicate holds when at least one of the arguments is ground
(otherwise, an error message will be displayed). The argument  _A_ must
be unifiable with an atom, and the argument  _L_ with the list of the
characters of  _A_.

 
*/
EOF
sed -e "2270r tmp" /Users/vsc/git/yap-6.3/C/atomic.c > x
     mv x /Users/vsc/git/yap-6.3/C/atomic.c

#false
cat << "EOF" > tmp
/** @pred  char_code(? _A_,? _I_) is iso 


The built-in succeeds with  _A_ bound to character represented as an
atom, and  _I_ bound to the character code represented as an
integer. At least, one of either  _A_ or  _I_ must be bound before
the call.

 
*/
EOF
sed -e "2259r tmp" /Users/vsc/git/yap-6.3/C/atomic.c > x
     mv x /Users/vsc/git/yap-6.3/C/atomic.c

#false
cat << "EOF" > tmp
/** @pred  name( _A_, _L_) 


The predicate holds when at least one of the arguments is ground
(otherwise, an error message will be displayed). The argument  _A_ will
be unified with an atomic symbol and  _L_ with the list of the ASCII
codes for the characters of the external representation of  _A_.

~~~~~{.prolog}
 name(yap,L).
~~~~~
will return:

~~~~~{.prolog}
 L = [121,97,112].
~~~~~
and

~~~~~{.prolog}
 name(3,L).
~~~~~
will return:

~~~~~{.prolog}
 L = [51].
~~~~~

 
*/
EOF
sed -e "2225r tmp" /Users/vsc/git/yap-6.3/C/atomic.c > x
     mv x /Users/vsc/git/yap-6.3/C/atomic.c

#false
cat << "EOF" > tmp
/** @pred  sub_atom(+ _A_,? _Bef_, ? _Size_, ? _After_, ? _At_out_) is iso 


True when  _A_ and  _At_out_ are atoms such that the name of
 _At_out_ has size  _Size_ and is a sub-string of the name of
 _A_, such that  _Bef_ is the number of characters before and
 _After_ the number of characters afterwards.

Note that  _A_ must always be known, but  _At_out_ can be unbound when
calling this built-in. If all the arguments for sub_atom/5 but  _A_
are unbound, the built-in will backtrack through all possible
sub-strings of  _A_.




 */
EOF
sed -e "2199r tmp" /Users/vsc/git/yap-6.3/C/atomic.c > x
     mv x /Users/vsc/git/yap-6.3/C/atomic.c

#false
cat << "EOF" > tmp
/** @pred attvar( _-Var_) 


Succeed if  _Var_ is an attributed variable.



 */
EOF
sed -e "1106r tmp" /Users/vsc/git/yap-6.3/C/attvar.c > x
     mv x /Users/vsc/git/yap-6.3/C/attvar.c

#false
cat << "EOF" > tmp
/** @pred  rational( _T_) 


Checks whether `T` is a rational number.

 
*/
EOF
sed -e "566r tmp" /Users/vsc/git/yap-6.3/C/bignum.c > x
     mv x /Users/vsc/git/yap-6.3/C/bignum.c

#false
cat << "EOF" > tmp
/** @pred  compare( _C_, _X_, _Y_) is iso 


As a result of comparing  _X_ and  _Y_,  _C_ may take one of
the following values:

+ 
`=` if  _X_ and  _Y_ are identical;
+ 
`<` if  _X_ precedes  _Y_ in the defined order;
+ 
`>` if  _Y_ precedes  _X_ in the defined order;


+ _X_ ==  _Y_ is iso 


Succeeds if terms  _X_ and  _Y_ are strictly identical. The
difference between this predicate and =/2 is that, if one of the
arguments is a free variable, it only succeeds when they have already
been unified.

~~~~~{.prolog}
?- X == Y.
~~~~~
fails, but,

~~~~~{.prolog}
?- X = Y, X == Y.
~~~~~
succeeds.

~~~~~{.prolog}
?- X == 2.
~~~~~
fails, but,

~~~~~{.prolog}
?- X = 2, X == 2.
~~~~~
succeeds.

 
*/
EOF
sed -e "932r tmp" /Users/vsc/git/yap-6.3/C/cmppreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/cmppreds.c

#false
cat << "EOF" > tmp
/** @pred  _X_ @>=  _Y_ is iso 


Term  _X_ does not precede term  _Y_ in the standard order.

 
*/
EOF
sed -e "931r tmp" /Users/vsc/git/yap-6.3/C/cmppreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/cmppreds.c

#false
cat << "EOF" > tmp
/** @pred  _X_ @>  _Y_ is iso 


Term  _X_ follows term  _Y_ in the standard order.

 
*/
EOF
sed -e "930r tmp" /Users/vsc/git/yap-6.3/C/cmppreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/cmppreds.c

#false
cat << "EOF" > tmp
/** @pred  _X_ @=<  _Y_ is iso 


Term  _X_ does not follow term  _Y_ in the standard order.

 
*/
EOF
sed -e "929r tmp" /Users/vsc/git/yap-6.3/C/cmppreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/cmppreds.c

#false
cat << "EOF" > tmp
/** @pred  _X_ @<  _Y_ is iso 


Term  _X_ precedes term  _Y_ in the standard order.

 
*/
EOF
sed -e "928r tmp" /Users/vsc/git/yap-6.3/C/cmppreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/cmppreds.c

#false
cat << "EOF" > tmp
/** @pred  _X_ \==  _Y_ is iso 


Terms  _X_ and  _Y_ are not strictly identical.

 
*/
EOF
sed -e "927r tmp" /Users/vsc/git/yap-6.3/C/cmppreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/cmppreds.c

#false
cat << "EOF" > tmp
/** @pred  key_statistics(+ _K_,- _Entries_,- _Size_,- _IndexSize_) 


Returns several statistics for a key  _K_. Currently, it says how
many entries we have for that key,  _Entries_, what is the
total size spent on entries,  _Size_, and what is the amount of
space spent in indices.

 
*/
EOF
sed -e "5684r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred  eraseall(+ _K_) 


All terms belonging to the key `K` are erased from the internal
database. The predicate always succeeds.

 
*/
EOF
sed -e "5667r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred  instance(+ _R_,- _T_) 


If  _R_ refers to a clause or a recorded term,  _T_ is unified
with its most general instance. If  _R_ refers to an unit clause
 _C_, then  _T_ is unified with ` _C_ :- true`. When
 _R_ is not a reference to an existing clause or to a recorded term,
this goal fails.

 
*/
EOF
sed -e "5665r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred  erased(+ _R_) 


Succeeds if the object whose database reference is  _R_ has been
erased.

 
*/
EOF
sed -e "5664r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred  erase(+ _R_) 


The term referred to by  _R_ is erased from the internal database. If
reference  _R_ does not exist in the database, `erase` just fails.

 
*/
EOF
sed -e "5659r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred  recordz_at(+ _R0_, _T_,- _R_) 


Makes term  _T_ the record following record with reference
 _R0_, and unifies  _R_ with its reference.

 
*/
EOF
sed -e "5654r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred  recorda_at(+ _R0_, _T_,- _R_) 


Makes term  _T_ the record preceding record with reference
 _R0_, and unifies  _R_ with its reference.

 
*/
EOF
sed -e "5653r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred  recordz(+ _K_, _T_,- _R_) 


Makes term  _T_ the last record under key  _K_ and unifies  _R_
with its reference.

 
*/
EOF
sed -e "5651r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred  recorda(+ _K_, _T_,- _R_) 


Makes term  _T_ the first record under key  _K_ and  unifies  _R_
with its reference.

 
*/
EOF
sed -e "5642r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred  recorded(+ _K_, _T_, _R_) 


Searches in the internal database under the key  _K_, a term that
unifies with  _T_ and whose reference matches  _R_. This
built-in may be used in one of two ways:

+ _K_ may be given, in this case the built-in will return all
elements of the internal data-base that match the key.
+ _R_ may be given, if so returning the key and element that
match the reference.


 
*/
EOF
sed -e "5626r tmp" /Users/vsc/git/yap-6.3/C/dbase.c > x
     mv x /Users/vsc/git/yap-6.3/C/dbase.c

#false
cat << "EOF" > tmp
/** @pred between(+ _Low_,+ _High_,? _Value_) 



 _Low_ and  _High_ are integers,  _High_ less or equal than
 _Low_. If  _Value_ is an integer,  _Low_ less or equal than
 _Value_ less or equal than  _High_.  When  _Value_ is a
variable it is successively bound to all integers between  _Low_ and
 _High_.  If  _High_ is `inf`, between/3 is true iff
 _Value_ less or equal than  _Low_, a feature that is particularly
interesting for generating integers from a certain value.

 
*/
EOF
sed -e "622r tmp" /Users/vsc/git/yap-6.3/C/eval.c > x
     mv x /Users/vsc/git/yap-6.3/C/eval.c

#false
cat << "EOF" > tmp
/** @pred nb_delete(? _Name_)

Delete the named global variable.



 */
EOF
sed -e "2850r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred  nb_delete(+ _Name_)  


Delete the named global variable. 


Global variables have been introduced by various Prolog
implementations recently. We follow the implementation of them in
SWI-Prolog, itself based on hProlog by Bart Demoen.

GNU-Prolog provides a rich set of global variables, including
arrays. Arrays can be implemented easily in YAP and SWI-Prolog using
functor/3 and `setarg/3` due to the unrestricted arity of
compound terms.


 */
EOF
sed -e "2850r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred  nb_linkarg(+ _Arg_, + _Term_, + _Value_)  



As nb_setarg/3, but like nb_linkval/2 it does not
duplicate  _Value_. Use with extreme care and consult the
documentation of nb_linkval/2 before use.

 
*/
EOF
sed -e "2839r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred  nb_set_shared_arg(+ _Arg_, + _Term_, + _Value_)  



As nb_setarg/3, but like nb_linkval/2 it does not
duplicate the global sub-terms in  _Value_. Use with extreme care
and consult the documentation of nb_linkval/2 before use.

 
*/
EOF
sed -e "2828r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred  nb_setarg(+{Arg], + _Term_, + _Value_) 



Assigns the  _Arg_-th argument of the compound term  _Term_ with
the given  _Value_ as setarg/3, but on backtracking the assignment
is not reversed. If  _Term_ is not atomic, it is duplicated using
duplicate_term/2. This predicate uses the same technique as
nb_setval/2. We therefore refer to the description of
nb_setval/2 for details on non-backtrackable assignment of
terms. This predicate is compatible to GNU-Prolog
`setarg(A,T,V,false)`, removing the type-restriction on
 _Value_. See also nb_linkarg/3. Below is an example for
counting the number of solutions of a goal. Note that this
implementation is thread-safe, reentrant and capable of handling
exceptions. Realising these features with a traditional implementation
based on assert/retract or flag/3 is much more complicated.

~~~~~
    succeeds_n_times(Goal, Times) :-
            Counter = counter(0),
            (   Goal,
                arg(1, Counter, N0),
                N is N0 + 1,
                nb_setarg(1, Counter, N),
                fail
            ;   arg(1, Counter, Times)
            ).
~~~~~

 
*/
EOF
sed -e "2795r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred  nb_linkval(+ _Name_, + _Value_)  


Associates the term  _Value_ with the atom  _Name_ without
copying it. This is a fast special-purpose variation of nb_setval/2
intended for expert users only because the semantics on backtracking
to a point before creating the link are poorly defined for compound
terms. The principal term is always left untouched, but backtracking
behaviour on arguments is undone if the original assignment was
trailed and left alone otherwise, which implies that the history that
created the term affects the behaviour on backtracking. Please
consider the following example:

~~~~~
demo_nb_linkval :-
        T = nice(N),
        (   N = world,
            nb_linkval(myvar, T),
            fail
        ;   nb_getval(myvar, V),
            writeln(V)
        ).
~~~~~

 
*/
EOF
sed -e "2767r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred  nb_set_shared_val(+ _Name_, + _Value_)  


Associates the term  _Value_ with the atom  _Name_, but sharing
non-backtrackable terms. This may be useful if you want to rewrite a
global variable so that the new copy will survive backtracking, but
you want to share structure with the previous term.

The next example shows the differences between the three built-ins:

~~~~~
?- nb_setval(a,a(_)),nb_getval(a,A),nb_setval(b,t(C,A)),nb_getval(b,B).
A = a(_A),
B = t(_B,a(_C)) ? 

?- nb_setval(a,a(_)),nb_getval(a,A),nb_set_shared_val(b,t(C,A)),nb_getval(b,B).

?- nb_setval(a,a(_)),nb_getval(a,A),nb_linkval(b,t(C,A)),nb_getval(b,B).
A = a(_A),
B = t(C,a(_A)) ?
~~~~~

 
*/
EOF
sed -e "2742r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred nb_setval(+ _Name_,+ _Value_) 


Associates a copy of  _Value_ created with duplicate_term/2
with the atom  _Name_.  Note that this can be used to set an
initial value other than `[]` prior to backtrackable assignment.

 
*/
EOF
sed -e "2723r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred  nb_setval(+ _Name_, + _Value_)  


Associates a copy of  _Value_ created with duplicate_term/2 with
the atom  _Name_. Note that this can be used to set an initial
value other than `[]` prior to backtrackable assignment.

 
*/
EOF
sed -e "2723r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred b_setval(+ _Name_,+ _Value_) 


Associate the term  _Value_ with the atom  _Name_ or replaces
the currently associated value with  _Value_.  If  _Name_ does
not refer to an existing global variable a variable with initial value
`[]` is created (the empty list).  On backtracking the
assignment is reversed.

 
*/
EOF
sed -e "2700r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred  b_setval(+ _Name_, + _Value_)  


Associate the term  _Value_ with the atom  _Name_ or replaces
the currently associated value with  _Value_. If  _Name_ does
not refer to an existing global variable a variable with initial value
[] is created (the empty list). On backtracking the assignment is
reversed. 

 
*/
EOF
sed -e "2700r tmp" /Users/vsc/git/yap-6.3/C/globals.c > x
     mv x /Users/vsc/git/yap-6.3/C/globals.c

#false
cat << "EOF" > tmp
/** @pred  functor( _T_, _F_, _N_) is iso 


The top functor of term  _T_ is named  _F_ and has  arity  _N_.

When  _T_ is not instantiated,  _F_ and  _N_ must be. If
 _N_ is 0,  _F_ must be an atomic symbol, which will be unified
with  _T_. If  _N_ is not 0, then  _F_ must be an atom and
 _T_ becomes instantiated to the most general term having functor
 _F_ and arity  _N_. If  _T_ is instantiated to a term then
 _F_ and  _N_ are respectively unified with its top functor name
and arity.

In the current version of YAP the arity  _N_ must be an
integer. Previous versions allowed evaluable expressions, as long as the
expression would evaluate to an integer. This feature is not available
in the ISO Prolog standard.

 
*/
EOF
sed -e "1108r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  _X_ \=  _Y_ is iso 


Succeeds if terms  _X_ and  _Y_ are not unifiable.

 
*/
EOF
sed -e "1105r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  _X_ =  _Y_ is iso 


Tries to unify terms  _X_ and  _Y_.

 
*/
EOF
sed -e "1104r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  float( _T_) is iso 


Checks whether  _T_ is a floating point number.

 
*/
EOF
sed -e "1103r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  compound( _T_) is iso 


Checks whether  _T_ is a compound term.

 
*/
EOF
sed -e "1102r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  db_reference( _T_) 


Checks whether  _T_ is a database reference.

 
*/
EOF
sed -e "1100r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  var( _T_) is iso 


Succeeds if  _T_ is currently a free variable, otherwise fails. 

 
*/
EOF
sed -e "1099r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  number( _T_) is iso 


Checks whether `T` is an integer, rational or a float.

 
*/
EOF
sed -e "1098r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  nonvar( _T_) is iso 


The opposite of `var( _T_)`.

 
*/
EOF
sed -e "1097r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  integer( _T_) is iso 


Succeeds if and only if  _T_ is currently instantiated to an  integer.

 
*/
EOF
sed -e "1096r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  atomic(T) is iso 


Checks whether  _T_ is an atomic symbol (atom or number).

 
*/
EOF
sed -e "1095r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  atom( _T_) is iso 


Succeeds if and only if  _T_ is currently instantiated to an  atom.

 
*/
EOF
sed -e "1094r tmp" /Users/vsc/git/yap-6.3/C/inlines.c > x
     mv x /Users/vsc/git/yap-6.3/C/inlines.c

#false
cat << "EOF" > tmp
/** @pred  stream_select(+ _STREAMS_,+ _TIMEOUT_,- _READSTREAMS_) 


Given a list of open  _STREAMS_ opened in read mode and a  _TIMEOUT_
return a list of streams who are now available for reading. 

If the  _TIMEOUT_ is instantiated to `off`,
stream_select/3 will wait indefinitely for a stream to become
open. Otherwise the timeout must be of the form `SECS:USECS` where
`SECS` is an integer gives the number of seconds to wait for a timeout
and `USECS` adds the number of micro-seconds.

This built-in is only defined if the system call `select` is
available in the system.

 
*/
EOF
sed -e "1024r tmp" /Users/vsc/git/yap-6.3/C/iopreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/iopreds.c

#false
cat << "EOF" > tmp
/** @pred char_conversion(+ _IN_,+ _OUT_) is iso 


While reading terms convert unquoted occurrences of the character
 _IN_ to the character  _OUT_. Both  _IN_ and  _OUT_ must be
bound to single characters atoms.

Character conversion only works if the flag `char_conversion` is
on. This is default in the `iso` and `sicstus` language
modes. As an example, character conversion can be used for instance to
convert characters from the ISO-LATIN-1 character set to ASCII.

If  _IN_ is the same character as  _OUT_, char_conversion/2
will remove this conversion from the table.

 
*/
EOF
sed -e "1001r tmp" /Users/vsc/git/yap-6.3/C/iopreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/iopreds.c

#false
cat << "EOF" > tmp
/** @pred close_shared_object(+ _Handle_) 

Detach the shared object identified by  _Handle_. 

 
*/
EOF
sed -e "236r tmp" /Users/vsc/git/yap-6.3/C/load_foreign.c > x
     mv x /Users/vsc/git/yap-6.3/C/load_foreign.c

#false
cat << "EOF" > tmp
/** @pred  is_mutable(? _D_) 


Holds if  _D_ is a mutable term.

 
*/
EOF
sed -e "351r tmp" /Users/vsc/git/yap-6.3/C/mavar.c > x
     mv x /Users/vsc/git/yap-6.3/C/mavar.c

#false
cat << "EOF" > tmp
/** @pred  update_mutable(+ _D_,+ _M_) 


Set the current value of mutable term  _M_ to term  _D_.



 */
EOF
sed -e "350r tmp" /Users/vsc/git/yap-6.3/C/mavar.c > x
     mv x /Users/vsc/git/yap-6.3/C/mavar.c

#false
cat << "EOF" > tmp
/** @pred  get_mutable(? _D_,+ _M_) 


Unify the current value of mutable term  _M_ with term  _D_.

 
*/
EOF
sed -e "349r tmp" /Users/vsc/git/yap-6.3/C/mavar.c > x
     mv x /Users/vsc/git/yap-6.3/C/mavar.c

#false
cat << "EOF" > tmp
/** @pred  create_mutable(+ _D_,- _M_) 


Create new mutable variable  _M_ with initial value  _D_.

 
*/
EOF
sed -e "348r tmp" /Users/vsc/git/yap-6.3/C/mavar.c > x
     mv x /Users/vsc/git/yap-6.3/C/mavar.c

#false
cat << "EOF" > tmp
/** @pred  setarg(+ _I_,+ _S_,? _T_) 


Set the value of the  _I_th argument of term  _S_ to term  _T_. 

 
*/
EOF
sed -e "347r tmp" /Users/vsc/git/yap-6.3/C/mavar.c > x
     mv x /Users/vsc/git/yap-6.3/C/mavar.c

#false
cat << "EOF" > tmp
/** @pred  abort 


Abandons the execution of the current goal and returns to top level. All
break levels (see break/0 below) are terminated. It is mainly
used during debugging or after a serious execution error, to return to
the top-level.

 
*/
EOF
sed -e "1997r tmp" /Users/vsc/git/yap-6.3/C/stdpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/stdpreds.c

#false
cat << "EOF" > tmp
/** @pred  _T_ =..  _L_ is iso 


The list  _L_ is built with the functor and arguments of the term
 _T_. If  _T_ is instantiated to a variable, then  _L_ must be
instantiated either to a list whose head is an atom, or to a list
consisting of just a number.

 
*/
EOF
sed -e "1955r tmp" /Users/vsc/git/yap-6.3/C/stdpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/stdpreds.c

#false
cat << "EOF" > tmp
/** @pred  get_value(+ _A_,- _V_) 


In YAP, atoms can be associated with constants. If one such
association exists for atom  _A_, unify the second argument with the
constant. Otherwise, unify  _V_ with `[]`.

This predicate is YAP specific.

 
*/
EOF
sed -e "1939r tmp" /Users/vsc/git/yap-6.3/C/stdpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/stdpreds.c

#false
cat << "EOF" > tmp
/** @pred  set_value(+ _A_,+ _C_) 


Associate atom  _A_ with constant  _C_.

The `set_value` and `get_value` built-ins give a fast alternative to
the internal data-base. This is a simple form of implementing a global
counter.

~~~~~
       read_and_increment_counter(Value) :-
                get_value(counter, Value),
                Value1 is Value+1,
                set_value(counter, Value1).
~~~~~
This predicate is YAP specific.




 
*/
EOF
sed -e "1916r tmp" /Users/vsc/git/yap-6.3/C/stdpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/stdpreds.c

#false
cat << "EOF" > tmp
/** @pred  rename(+ _F_,+ _G_) 


Renames file  _F_ to  _G_.

 
*/
EOF
sed -e "3095r tmp" /Users/vsc/git/yap-6.3/C/sysbits.c > x
     mv x /Users/vsc/git/yap-6.3/C/sysbits.c

#false
cat << "EOF" > tmp
/** @pred  sh 


Creates a new shell interaction.

 
*/
EOF
sed -e "3092r tmp" /Users/vsc/git/yap-6.3/C/sysbits.c > x
     mv x /Users/vsc/git/yap-6.3/C/sysbits.c

#false
cat << "EOF" > tmp
/** @pred mutex_unlock(+ _MutexId_) 


Unlock the mutex. This can only be called if the mutex is held by the
calling thread. If this is not the case, a `permission_error`
exception is raised.

 
*/
EOF
sed -e "1682r tmp" /Users/vsc/git/yap-6.3/C/threads.c > x
     mv x /Users/vsc/git/yap-6.3/C/threads.c

#false
cat << "EOF" > tmp
/** @pred mutex_trylock(+ _MutexId_) 


As mutex_lock/1, but if the mutex is held by another thread, this
predicates fails immediately.

 
*/
EOF
sed -e "1681r tmp" /Users/vsc/git/yap-6.3/C/threads.c > x
     mv x /Users/vsc/git/yap-6.3/C/threads.c

#false
cat << "EOF" > tmp
/** @pred mutex_lock(+ _MutexId_) 


Lock the mutex.  Prolog mutexes are <em>recursive</em> mutexes: they
can be locked multiple times by the same thread.  Only after unlocking
it as many times as it is locked, the mutex becomes available for
locking by other threads. If another thread has locked the mutex the
calling thread is suspended until to mutex is unlocked.

If  _MutexId_ is an atom, and there is no current mutex with that
name, the mutex is created automatically using mutex_create/1.  This
implies named mutexes need not be declared explicitly.

Please note that locking and unlocking mutexes should be paired
carefully. Especially make sure to unlock mutexes even if the protected
code fails or raises an exception. For most common cases use
with_mutex/2, which provides a safer way for handling Prolog-level
mutexes.

 
*/
EOF
sed -e "1680r tmp" /Users/vsc/git/yap-6.3/C/threads.c > x
     mv x /Users/vsc/git/yap-6.3/C/threads.c

#false
cat << "EOF" > tmp
/** @pred mutex_destroy(+ _MutexId_) 


Destroy a mutex.  After this call,  _MutexId_ becomes invalid and
further references yield an `existence_error` exception.

 
*/
EOF
sed -e "1679r tmp" /Users/vsc/git/yap-6.3/C/threads.c > x
     mv x /Users/vsc/git/yap-6.3/C/threads.c

#false
cat << "EOF" > tmp
/** @pred mutex_create(? _MutexId_) 


Create a mutex.  if  _MutexId_ is an atom, a <em>named</em> mutex is
created.  If it is a variable, an anonymous mutex reference is returned.
There is no limit to the number of mutexes that can be created.

 
*/
EOF
sed -e "1678r tmp" /Users/vsc/git/yap-6.3/C/threads.c > x
     mv x /Users/vsc/git/yap-6.3/C/threads.c

#false
cat << "EOF" > tmp
/** @pred thread_setconcurrency(+ _Old_, - _New_) 


Determine the concurrency of the process, which is defined as the
maximum number of concurrently active threads. `Active` here means
they are using CPU time. This option is provided if the
thread-implementation provides
`pthread_setconcurrency()`. Solaris is a typical example of this
family. On other systems this predicate unifies  _Old_ to 0 (zero)
and succeeds silently.

 
*/
EOF
sed -e "1663r tmp" /Users/vsc/git/yap-6.3/C/threads.c > x
     mv x /Users/vsc/git/yap-6.3/C/threads.c

#false
cat << "EOF" > tmp
/** @pred thread_yield 


Voluntarily relinquish the processor.

 
*/
EOF
sed -e "1651r tmp" /Users/vsc/git/yap-6.3/C/threads.c > x
     mv x /Users/vsc/git/yap-6.3/C/threads.c

#false
cat << "EOF" > tmp
/** @pred stop_low_level_trace 


Stop display of messages at procedure entry and retry.


Note that this compile-time option will slow down execution.


 */
EOF
sed -e "462r tmp" /Users/vsc/git/yap-6.3/C/tracer.c > x
     mv x /Users/vsc/git/yap-6.3/C/tracer.c

#false
cat << "EOF" > tmp
/** @pred start_low_level_trace 


Begin display of messages at procedure entry and retry.

 
*/
EOF
sed -e "451r tmp" /Users/vsc/git/yap-6.3/C/tracer.c > x
     mv x /Users/vsc/git/yap-6.3/C/tracer.c

#false
cat << "EOF" > tmp
/** @pred  acyclic_term( _T_) is iso 


Succeeds if there are loops in the term  _T_, that is, it is an infinite term.

 
*/
EOF
sed -e "1024r tmp" /Users/vsc/git/yap-6.3/C/unify.c > x
     mv x /Users/vsc/git/yap-6.3/C/unify.c

#false
cat << "EOF" > tmp
/** @pred  unify_with_occurs_check(?T1,?T2) is iso 


Obtain the most general unifier of terms  _T1_ and  _T2_, if there
is one.

This predicate implements the full unification algorithm. An example:n

~~~~~{.prolog}
unify_with_occurs_check(a(X,b,Z),a(X,A,f(B)).
~~~~~
will succeed with the bindings `A = b` and `Z = f(B)`. On the
other hand:

~~~~~{.prolog}
unify_with_occurs_check(a(X,b,Z),a(X,A,f(Z)).
~~~~~
would fail, because `Z` is not unifiable with `f(Z)`. Note that
`(=)/2` would succeed for the previous examples, giving the following
bindings `A = b` and `Z = f(Z)`.

 
*/
EOF
sed -e "1000r tmp" /Users/vsc/git/yap-6.3/C/unify.c > x
     mv x /Users/vsc/git/yap-6.3/C/unify.c

#false
cat << "EOF" > tmp
/** @pred  unnumbervars( _T_,+ _NT_) 


Replace every `$VAR( _I_)` by a free variable.

 
*/
EOF
sed -e "5388r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred  numbervars( _T_,+ _N1_,- _Nn_) 


Instantiates each variable in term  _T_ to a term of the form:
`$VAR( _I_)`, with  _I_ increasing from  _N1_ to  _Nn_.

 
*/
EOF
sed -e "5379r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred  term_factorized(? _TI_,- _TF_, ?SubTerms) 


Similar to rational_term_to_tree/4, but _SubTerms_ is a proper list.

 
*/
EOF
sed -e "5370r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred  rational_term_to_tree(? _TI_,- _TF_, ?SubTerms, ?MoreSubterms) 


The term _TF_ is a forest representation (without cycles and repeated
terms) for the Prolog term _TI_. The term _TF_ is the main term.  The
difference list _SubTerms_-_MoreSubterms_ stores terms of the form
_V=T_, where _V_ is a new variable occuring in _TF_, and _T_ is a copy
of a sub-term from _TI_.

 
*/
EOF
sed -e "5358r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred term_attvars(+ _Term_,- _AttVars_) 


 _AttVars_ is a list of all attributed variables in  _Term_ and
its attributes. I.e., term_attvars/2 works recursively through
attributes.  This predicate is Cycle-safe.

 
*/
EOF
sed -e "5346r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred  term_variables(? _Term_, - _Variables_) is iso 



Unify  _Variables_ with the list of all variables of term
 _Term_.  The variables occur in the order of their first
appearance when traversing the term depth-first, left-to-right.

 
*/
EOF
sed -e "5334r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred  ground( _T_) is iso 


Succeeds if there are no free variables in the term  _T_.

 
*/
EOF
sed -e "5323r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred copy_term_nat(? _TI_,- _TF_)  


As copy_term/2.  Attributes however, are <em>not</em> copied but replaced
by fresh variables.




 */
EOF
sed -e "5312r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred  duplicate_term(? _TI_,- _TF_) 


Term  _TF_ is a variant of the original term  _TI_, such that
for each variable  _V_ in the term  _TI_ there is a new variable
 _V'_ in term  _TF_, and the two terms do not share any
structure. All suspended goals and attributes for attributed variables
in  _TI_ are also duplicated.

Also refer to copy_term/2.

 
*/
EOF
sed -e "5298r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred  copy_term(? _TI_,- _TF_) is iso 


Term  _TF_ is a variant of the original term  _TI_, such that for
each variable  _V_ in the term  _TI_ there is a new variable  _V'_
in term  _TF_. Notice that:

+ suspended goals and attributes for attributed variables in _TI_ are also duplicated;
+ ground terms are shared between the new and the old term.

If you do not want any sharing to occur please use
duplicate_term/2.

 
*/
EOF
sed -e "5282r tmp" /Users/vsc/git/yap-6.3/C/utilpreds.c > x
     mv x /Users/vsc/git/yap-6.3/C/utilpreds.c

#false
cat << "EOF" > tmp
/** @pred abolish_all_tables/0 


Removes all the entries from the table space for all tabled
predicates. The predicates remain as tabled predicates.

 
*/
EOF
sed -e "210r tmp" /Users/vsc/git/yap-6.3/OPTYap/opt.preds.c > x
     mv x /Users/vsc/git/yap-6.3/OPTYap/opt.preds.c

#false
cat << "EOF" > tmp
/** @pred put_assoc(+ _Key_,+ _Assoc_,+ _Val_,+ _New_) 


The association list  _New_ includes and element of association
 _key_ with  _Val_, and all elements of  _Assoc_ that did not
have key  _Key_.




 */
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred ord_list_to_assoc(+ _List_,? _Assoc_) 


Given an ordered list  _List_ such that each element of  _List_ is
of the form  _Key-Val_, and all the  _Keys_ are unique,  _Assoc_ is
the corresponding association list.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred min_assoc(+ _Assoc_,- _Key_,? _Value_) 


Given the association list
 _Assoc_,  _Key_ in the smallest key in the list, and  _Value_
the associated value.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred max_assoc(+ _Assoc_,- _Key_,? _Value_) 


Given the association list
 _Assoc_,  _Key_ in the largest key in the list, and  _Value_
the associated value.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred map_assoc(+ _Pred_,+ _Assoc_,? _New_)

Given the binary predicate name  _Pred_ and the association list
 _Assoc_,  _New_ in an association list with keys in  _Assoc_,
and such that if  _Key-Val_ is in  _Assoc_, and  _Key-Ans_ is in
 _New_, then  _Pred_( _Val_, _Ans_) holds.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred map_assoc(+ _Pred_,+ _Assoc_) 


Succeeds if the unary predicate name  _Pred_( _Val_) holds for every
element in the association list.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred list_to_assoc(+ _List_,? _Assoc_) 


Given a list  _List_ such that each element of  _List_ is of the
form  _Key-Val_, and all the  _Keys_ are unique,  _Assoc_ is
the corresponding association list.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred is_assoc(+ _Assoc_) 


Succeeds if  _Assoc_ is an association list, that is, if it is a
red-black tree.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred get_prev_assoc(+ _Key_,+ _Assoc_,? _Next_,? _Value_) 


If  _Key_ is one of the elements in the association list  _Assoc_,
return the previous key,  _Next_, and its value,  _Value_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred get_next_assoc(+ _Key_,+ _Assoc_,? _Next_,? _Value_)

If  _Key_ is one of the elements in the association list  _Assoc_,
return the next key,  _Next_, and its value,  _Value_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred get_assoc(+ _Key_,+ _Assoc_,? _Value_,+ _NAssoc_,? _NValue_) 


If  _Key_ is one of the elements in the association list  _Assoc_,
return the associated value  _Value_ and a new association list
 _NAssoc_ where  _Key_ is associated with  _NValue_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred get_assoc(+ _Key_,+ _Assoc_,? _Value_) 


If  _Key_ is one of the elements in the association list  _Assoc_,
return the associated value.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred gen_assoc(+ _Assoc_,? _Key_,? _Value_) 


Given the association list  _Assoc_, unify  _Key_ and  _Value_
with two associated elements. It can be used to enumerate all elements
in the association list.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred empty_assoc(+ _Assoc_) 


Succeeds if association list  _Assoc_ is empty.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred del_min_assoc(+ _Assoc_, ? _Key_, ? _Val_, ? _NewAssoc_) 


Succeeds if  _NewAssoc_ is an association list, obtained by removing
the smallest element of the list, with  _Key_ and  _Val_
from the list  _Assoc_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred del_max_assoc(+ _Assoc_, ? _Key_, ? _Val_, ? _NewAssoc_) 


Succeeds if  _NewAssoc_ is an association list, obtained by removing
the largest element of the list, with  _Key_ and  _Val_ from the
list  _Assoc_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred del_assoc(+ _Key_, + _Assoc_, ? _Val_, ? _NewAssoc_) 


Succeeds if  _NewAssoc_ is an association list, obtained by removing
the element with  _Key_ and  _Val_ from the list  _Assoc_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred assoc_to_list(+ _Assoc_,? _List_) 


Given an association list  _Assoc_ unify  _List_ with a list of
the form  _Key-Val_, where the elements  _Key_ are in ascending
order.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/assoc.yap > x
     mv x /Users/vsc/git/yap-6.3/library/assoc.yap

#false
cat << "EOF" > tmp
/** @pred avl_new(+ _T_) 


Create a new tree.

 
*/
EOF
sed -e "62r tmp" /Users/vsc/git/yap-6.3/library/avl.yap > x
     mv x /Users/vsc/git/yap-6.3/library/avl.yap

#false
cat << "EOF" > tmp
/** @pred avl_lookup(+ _Key_,- _Value_,+ _T_) 


Lookup an element with key  _Key_ in the AVL tree
 _T_, returning the value  _Value_.




 */
EOF
sed -e "62r tmp" /Users/vsc/git/yap-6.3/library/avl.yap > x
     mv x /Users/vsc/git/yap-6.3/library/avl.yap

#false
cat << "EOF" > tmp
/** @pred avl_insert(+ _Key_,? _Value_,+ _T0_,- _TF_) 


Add an element with key  _Key_ and  _Value_ to the AVL tree
 _T0_ creating a new AVL tree  _TF_. Duplicated elements are
allowed.

 
*/
EOF
sed -e "62r tmp" /Users/vsc/git/yap-6.3/library/avl.yap > x
     mv x /Users/vsc/git/yap-6.3/library/avl.yap

#true
cat << "EOF" > tmp
/** @pred process(+ _StreamInp_, + _Goal_) 



For every line  _LineIn_ in stream  _StreamInp_, call
`call(Goal,LineIn)`.

 
*/
EOF
sed -e "395r tmp" /Users/vsc/git/yap-6.3/library/block_diagram.yap > x
     mv x /Users/vsc/git/yap-6.3/library/block_diagram.yap

#false
cat << "EOF" > tmp
/** @pred make_diagram(+inputfilename, +ouputfilename, +predicate, +depth, +extension)


The same as make_diagram/2 but you can define how many of the imported/exporeted predicates will be shown with predicate, and how deep the crawler is allowed to go with depth. The extension is used if the file use module directives do not include a file extension.



*/
EOF
sed -e "214r tmp" /Users/vsc/git/yap-6.3/library/block_diagram.yap > x
     mv x /Users/vsc/git/yap-6.3/library/block_diagram.yap

#false
cat << "EOF" > tmp
/** @pred make_diagram(+inputfilename, +ouputfilename) 



This will crawl the files following the use_module, ensure_loaded directives withing the inputfilename.
The result will be a file in dot format.
You can make a pdf at the shell by asking `dot -Tpdf filename > output.pdf`.

 
*/
EOF
sed -e "214r tmp" /Users/vsc/git/yap-6.3/library/block_diagram.yap > x
     mv x /Users/vsc/git/yap-6.3/library/block_diagram.yap

#true
cat << "EOF" > tmp
/** @pred write_to_chars(+ _Term_, - _Result_) 



Execute the built-in procedure write/1 with argument  _Term_
outputting the result to the string of character codes  _Result_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred write_to_chars(+ _Term_, - _Result0_, - _Result_)


Execute the built-in procedure write/1 with argument  _Term_
outputting the result to the difference list of character codes
 _Result-Result0_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred with_output_to_chars(? _Goal_, ? _Chars0_, - _Chars_)


Execute goal  _Goal_ such that its standard output will be sent to a
memory buffer. After successful execution the contents of the memory
buffer will be converted to the difference list of character codes
 _Chars-Chars0_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred with_output_to_chars(? _Goal_, - _Stream_, ? _Chars0_, - _Chars_)


Execute goal  _Goal_ such that its standard output will be sent to a
memory buffer. After successful execution the contents of the memory
buffer will be converted to the difference list of character codes
 _Chars-Chars0_ and  _Stream_ receives the stream corresponding to
the memory buffer.

 */
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred with_output_to_chars(? _Goal_, - _Chars_) 



Execute goal  _Goal_ such that its standard output will be sent to a
memory buffer. After successful execution the contents of the memory
buffer will be converted to the list of character codes  _Chars_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#true
cat << "EOF" > tmp
/** @pred term_to_atom(? _Term_,? _Atom_) 


Succeeds if  _Atom_ describes a term that unifies with  _Term_. When
 _Atom_ is instantiated  _Atom_ is converted and then unified with
 _Term_.  If  _Atom_ has no valid syntax, a `syntax_error`
exception is raised. Otherwise  _Term_ is `written` on  _Atom_
using write/1.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#true
cat << "EOF" > tmp
/** @pred term_to_atom(? _Term_, ? _Atom_) 


True if  _Atom_ describes a term that unifies with  _Term_. When
 _Atom_ is instantiated  _Atom_ is converted and then unified with
 _Term_. If  _Atom_ has no valid syntax, a syntax_error exception
is raised. Otherwise  _Term_ is `written` on  _Atom_ using
write_term/2 with the option quoted(true).

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#true
cat << "EOF" > tmp
/** @pred read_from_chars(+ _Chars_, - _Term_) 



Parse the list of character codes  _Chars_ and return the result in
the term  _Term_. The character codes to be read must terminate with
a dot character such that either (i) the dot character is followed by
blank characters; or (ii) the dot character is the last character in the
string.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred open_chars_stream(+ _Chars_, - _Stream_) 



Open the list of character codes  _Chars_ as a stream  _Stream_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred number_to_chars(+ _Number_, - _Result_) 



Convert the number  _Number_ to the string of character codes
 _Result_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred number_to_chars(+ _Number_, - _Result0_, - _Result_)


Convert the atom  _Number_ to the difference list of character codes
 _Result-Result0_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred format_to_chars(+ _Form_, + _Args_, - _Result_, - _Result0_)


Execute the built-in procedure format/2 with form  _Form_ and
arguments  _Args_ outputting the result to the difference list of
character codes  _Result-Result0_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred format_to_chars(+ _Form_, + _Args_, - _Result_) 



Execute the built-in procedure format/2 with form  _Form_ and
arguments  _Args_ outputting the result to the string of character
codes  _Result_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred atom_to_chars(+ _Atom_, - _Result_) 



Convert the atom  _Atom_ to the string of character codes
 _Result_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred atom_to_chars(+ _Atom_, - _Result0_, - _Result_)


Convert the atom  _Atom_ to the difference list of character codes
 _Result-Result0_.

 
*/
EOF
sed -e "17r tmp" /Users/vsc/git/yap-6.3/library/charsio.yap > x
     mv x /Users/vsc/git/yap-6.3/library/charsio.yap

#false
cat << "EOF" > tmp
/** @pred on_cleanup(+ _CleanUpGoal_) 


Any Predicate might registers a  _CleanUpGoal_. The
 _CleanUpGoal_ is put onto the current cleanup context. All such
CleanUpGoals are executed in reverse order of their registration when
the surrounding cleanup-context ends. This call will throw an exception
if a predicate tries to register a  _CleanUpGoal_ outside of any
cleanup-context.

 
*/
EOF
sed -e "2r tmp" /Users/vsc/git/yap-6.3/library/cleanup.yap > x
     mv x /Users/vsc/git/yap-6.3/library/cleanup.yap

#false
cat << "EOF" > tmp
/** @pred cleanup_all 


Calls all pending CleanUpGoals and resets the cleanup-system to an
initial state. Should only be used as one of the last calls in the
main program.



There are some private predicates which could be used in special
cases, such as manually setting up cleanup-contexts and registering
CleanUpGoals for other than the current cleanup-context.
Read the Source Luke.


 */
EOF
sed -e "2r tmp" /Users/vsc/git/yap-6.3/library/cleanup.yap > x
     mv x /Users/vsc/git/yap-6.3/library/cleanup.yap

#false
cat << "EOF" > tmp
/** @pred call_cleanup(: _Goal_) 


Execute goal  _Goal_ within a cleanup-context. Called predicates
might register cleanup Goals which are called right after the end of
the call to  _Goal_. Cuts and exceptions inside Goal do not prevent the
execution of the cleanup calls. <tt>call_cleanup</tt> might be nested.

 
*/
EOF
sed -e "2r tmp" /Users/vsc/git/yap-6.3/library/cleanup.yap > x
     mv x /Users/vsc/git/yap-6.3/library/cleanup.yap

#false
cat << "EOF" > tmp
/** @pred attr_portray_hook(+ _AttValue_,+ _Var_) 



Called by write_term/2 and friends for each attribute if the option
`attributes(portray)` is in effect.  If the hook succeeds the
attribute is considered printed.  Otherwise  `Module = ...` is
printed to indicate the existence of a variable.

 
*/
EOF
sed -e "304r tmp" /Users/vsc/git/yap-6.3/library/clp/clp_distinct.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clp_distinct.pl

#true
cat << "EOF" > tmp
/** @pred all_distinct( _Cs_,  _Vs_)

verifies whether all elements of a list are different. Also tests if
all the sums between a list of constants and a list of variables are
different.

This is a formulation of the queens problem that uses both versions of `all_different`:

~~~~~{.prolog}
queens(N, Queens) :-
    length(Queens, N),
    Queens ins 1..N,
    all_distinct(Queens),
    foldl(inc, Queens, Inc, 0, _), % [0, 1, 2, .... ]
    foldl(dec, Queens, Dec, 0, _), % [0, -1, -2, ... ]
    all_distinct(Inc,Queens),
    all_distinct(Dec,Queens),
    labeling([], Queens).

inc(_, I0, I0, I) :-
    I is I0+1.

dec(_, I0, I0, I) :-
    I is I0-1.
~~~~~

The next example uses `all_different/1` and the functionality of the matrix package to verify that all squares in
sudoku have a different value:

~~~~~{.prolog}
    foreach( [I,J] ins 0..2 ,
           all_different(M[I*3+(0..2),J*3+(0..2)]) ),
~~~~~

 
*/
EOF
sed -e "157r tmp" /Users/vsc/git/yap-6.3/library/clp/clp_distinct.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clp_distinct.pl

#true
cat << "EOF" > tmp
/** @pred transpose(+ _Graph_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained from  _Graph_ by
replacing all edges of the form  _V1-V2_ by edges of the form
 _V2-V1_. The cost is `O(|V|^2)`. In the next example:

~~~~~{.prolog}
?- transpose([1-[3,5],2-[4],3-[],
              4-[5],5-[],6-[],7-[],8-[]], NL).

NL = [1-[],2-[],3-[1],4-[2],5-[1,4],6-[],7-[],8-[]]
~~~~~
Notice that an undirected graph is its own transpose.

 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred scalar_product(+ _Cs_, + _Vs_, + _Rel_, ? _V_    )

The product of constant  _Cs_ by  _Vs_ must be in relation
 _Rel_ with  _V_ .

 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred labeling( _Opts_,  _Xs_)
performs labeling, several variable and value selection options are
available. The defaults are `min` and `min_step`.

Variable selection options are as follows:

+ leftmost
choose the first variable
+ min
choose one of the variables with smallest minimum value
+ max
choose one of the variables with greatest maximum value
+ ff
choose one of the most constrained variables, that is, with the smallest
domain.


Given that we selected a variable, the values chosen for branching may
be:

+ min_step
smallest value
+ max_step
largest value
+ bisect
median
+ enum
all value starting from the minimum.


 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred all_different( _Vs_    )

Verifies whether all elements of a list are different.
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred _X_ #\=  _Y_ is semidet
disequality
 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred _X_ #>=  _Y_ is semidet
larger or equal
 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred _X_ #>  _Y_ is semidet
larger
 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred _X_ #==>  _B_  is det
Reified implication
 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred _X_ #=<  _Y_ is semidet
smaller
 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred _X_ #=  _Y_ is semidet
equality
 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred _X_ #<==>  _B_  is det
reified equivalence
 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred _X_ #<  _Y_ is semidet
smaller or equal

Arguments to this constraint may be an arithmetic expression with <tt>+</tt>,
<tt>-</tt>, <tt>\\*</tt>, integer division <tt>/</tt>, <tt>min</tt>, <tt>max</tt>, <tt>sum</tt>,
<tt>count</tt>, and
<tt>abs</tt>. Boolean variables support conjunction (/\), disjunction (\/),
implication (=>), equivalence (<=>), and xor. The <tt>sum</tt> constraint allows  a two argument version using the
`where` conditional, in Zinc style. 

The send more money equation may be written as:

~~~~~{.prolog}
          1000*S + 100*E + 10*N + D +
          1000*M + 100*O + 10*R + E #=
10000*M + 1000*O + 100*N + 10*E + Y,
~~~~~

This example uses `where` to select from
column  _I_ the elements that have value under  _M_:

~~~~~{.prolog}
OutFlow[I] #= sum(J in 1..N where D[J,I]<M, X[J,I])
~~~~~

The <tt>count</tt> constraint counts the number of elements that match a
certain constant or variable (integer sets are not available).

 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#true
cat << "EOF" > tmp
/** @pred _X_ #<  _B_  is det
reified implication 

As an example. consider finding out the people who wanted to sit
next to a friend and that are are actually sitting together:

~~~~~{.prolog}
preference_satisfied(X-Y, B) :-
    abs(X - Y) #= 1 #<==> B.
~~~~~
Note that not all constraints may be reifiable.

 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/library/clp/clpfd.pl > x
     mv x /Users/vsc/git/yap-6.3/library/clp/clpfd.pl

#false
cat << "EOF" > tmp
/** @pred db_usage 


Give general overview of data-base usage in the system.

 
*/
EOF
sed -e "11r tmp" /Users/vsc/git/yap-6.3/library/dbusage.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dbusage.yap

#false
cat << "EOF" > tmp
/** @pred db_static(+ _Threshold_)

List memory usage for every static predicate. Predicate must use more
than  _Threshold_ bytes.

 
*/
EOF
sed -e "11r tmp" /Users/vsc/git/yap-6.3/library/dbusage.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dbusage.yap

#false
cat << "EOF" > tmp
/** @pred db_static 


List memory usage for every static predicate.

 
*/
EOF
sed -e "11r tmp" /Users/vsc/git/yap-6.3/library/dbusage.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dbusage.yap

#false
cat << "EOF" > tmp
/** @pred db_dynamic(+ _Threshold_)

List memory usage for every dynamic predicate. Predicate must use more
than  _Threshold_ bytes.




 */
EOF
sed -e "11r tmp" /Users/vsc/git/yap-6.3/library/dbusage.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dbusage.yap

#false
cat << "EOF" > tmp
/** @pred db_dynamic 


List memory usage for every dynamic predicate.

 
*/
EOF
sed -e "11r tmp" /Users/vsc/git/yap-6.3/library/dbusage.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dbusage.yap

#false
cat << "EOF" > tmp
/** @pred ugraph_to_dgraph( + _UGraph_, - _Graph_) 


Unify  _Graph_ with the directed graph obtain from  _UGraph_,
represented in the form used in the  _ugraphs_ unweighted graphs
library.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_vertices(+ _Graph_, - _Vertices_) 


Unify  _Vertices_ with all vertices appearing in graph
 _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_transpose(+ _Graph_, - _Transpose_) 


Unify  _NewGraph_ with a new graph obtained from  _Graph_ by
replacing all edges of the form  _V1-V2_ by edges of the form
 _V2-V1_. 

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_transitive_closure(+ _Graph_, - _Closure_) 


Unify  _Closure_ with the transitive closure of graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_top_sort(+ _Graph_, - _Vertices_, ? _Vertices0_)

Unify the difference list  _Vertices_- _Vertices0_ with the
topological sort of graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_top_sort(+ _Graph_, - _Vertices_) 


Unify  _Vertices_ with the topological sort of graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_to_ugraph(+ _Graph_, - _UGraph_) 


Unify  _UGraph_ with the representation used by the  _ugraphs_
unweighted graphs library, that is, a list of the form
 _V-Neighbors_, where  _V_ is a node and  _Neighbors_ the nodes
children.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_symmetric_closure(+ _Graph_, - _Closure_) 


Unify  _Closure_ with the symmetric closure of graph  _Graph_,
that is,  if  _Closure_ contains an edge  _U-V_ it must also
contain the edge  _V-U_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_reachable(+ _Vertex_, + _Graph_, ? _Edges_) 


The path  _Path_ is a path starting at vertex  _Vertex_ in graph
 _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_path(+ _Vertex_, + _Vertex1_, + _Graph_, ? _Path_)

The path  _Path_ is a path starting at vertex  _Vertex_ in graph
 _Graph_ and ending at path  _Vertex2_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_path(+ _Vertex_, + _Graph_, ? _Path_) 


The path  _Path_ is a path starting at vertex  _Vertex_ in graph
 _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_neighbours(+ _Vertex_, + _Graph_, - _Vertices_) 


Unify  _Vertices_ with the list of neighbours of vertex  _Vertex_
in  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_neighbors(+ _Vertex_, + _Graph_, - _Vertices_) 


Unify  _Vertices_ with the list of neighbors of vertex  _Vertex_
in  _Graph_. If the vertice is not in the graph fail.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_min_paths(+ _V1_, + _Graph_, - _Paths_) 


Unify the list  _Paths_ with the minimal cost paths from node
 _N1_ to the nodes in graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_min_path(+ _V1_, + _V1_, + _Graph_, - _Path_, ? _Costt_) 


Unify the list  _Path_ with the minimal cost path between nodes
 _N1_ and  _N2_ in graph  _Graph_. Path  _Path_ has cost
 _Cost_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_max_path(+ _V1_, + _V1_, + _Graph_, - _Path_, ? _Costt_) 


Unify the list  _Path_ with the maximal cost path between nodes
 _N1_ and  _N2_ in graph  _Graph_. Path  _Path_ has cost
 _Cost_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_leaves(+ _Graph_, ? _Vertices_) 


The vertices  _Vertices_ have no outgoing edge in graph
 _Graph_.




 */
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_isomorphic(+ _Vs_, + _NewVs_, + _G0_, - _GF_) 


Unify the list  _GF_ with the graph isomorphic to  _G0_ where 
vertices in  _Vs_ map to vertices in  _NewVs_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_edges(+ _Graph_, - _Edges_) 


Unify  _Edges_ with all edges appearing in graph
 _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_edge(+ _N1_, + _N2_, + _Graph_) 


Edge  _N1_- _N2_ is an edge in directed graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_del_vertices(+ _Graph_, + _Vertices_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by deleting the list of
vertices  _Vertices_ and all the edges that start from or go to a
vertex in  _Vertices_ to the graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_del_vertex(+ _Graph_, + _Vertex_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by deleting vertex
 _Vertex_ and all the edges that start from or go to  _Vertex_ to
the graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_del_edges(+ _Graph_, + _Edges_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by removing the list of
edges  _Edges_ from the graph  _Graph_. Notice that no vertices
are deleted.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_del_edge(+ _Graph_, + _N1_, + _N2_, - _NewGraph_) 


Succeeds if  _NewGraph_ unifies with a new graph obtained by
removing the edge  _N1_- _N2_ from the graph  _Graph_. Notice
that no vertices are deleted.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_compose(+ _Graph1_, + _Graph2_, - _ComposedGraph_) 


Unify  _ComposedGraph_ with a new graph obtained by composing
 _Graph1_ and  _Graph2_, ie,  _ComposedGraph_ has an edge
 _V1-V2_ iff there is a  _V_ such that  _V1-V_ in  _Graph1_
and  _V-V2_ in  _Graph2_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_complement(+ _Graph_, - _NewGraph_) 


Unify  _NewGraph_ with the graph complementary to  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_add_vertices(+ _Graph_, + _Vertices_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by adding the list of
vertices  _Vertices_ to the graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_add_vertices(+ _Graph_, + _Vertex_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by adding
vertex  _Vertex_ to the graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_add_edges(+ _Graph_, + _Edges_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by adding the list of
edges  _Edges_ to the graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#false
cat << "EOF" > tmp
/** @pred dgraph_add_edge(+ _Graph_, + _N1_, + _N2_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by adding the edge
 _N1_- _N2_ to the graph  _Graph_.

 
*/
EOF
sed -e "277r tmp" /Users/vsc/git/yap-6.3/library/dgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dgraphs.yap

#true
cat << "EOF" > tmp
/** @pred foreach(:Generator, : _Goal_) 


True if the conjunction of instances of  _Goal_ using the
bindings from Generator is true. Unlike forall/2, which runs a
failure-driven loop that proves  _Goal_ for each solution of
Generator, foreach creates a conjunction. Each member of the
conjunction is a copy of  _Goal_, where the variables it shares
with Generator are filled with the values from the corresponding
solution.

The implementation executes forall/2 if  _Goal_ does not contain
any variables that are not shared with Generator.

Here is an example:

~~~~~{.prolog}
    ?- foreach( between(1,4,X), dif(X,Y)), Y = 5.
    Y = 5
    ?- foreach( between(1,4,X), dif(X,Y)), Y = 3.
    No
~~~~~

Notice that  _Goal_ is copied repeatedly, which may cause
problems if attributed variables are involved.

 
*/
EOF
sed -e "222r tmp" /Users/vsc/git/yap-6.3/library/dialect/bprolog/foreach.pl > x
     mv x /Users/vsc/git/yap-6.3/library/dialect/bprolog/foreach.pl

#true
cat << "EOF" > tmp
/** @pred foreach( _Sequence_,  _Goal_) 


Deterministic iterator. The ranges are given by  _Sequence_ that is
either ` _I_ in  _M_.. _N_`, or of the form 
`[ _I_, _J_] ins  _M_.. _N_`, or a list of the above conditions. 

Variables in the goal are assumed to be global, ie, share a single value
in the execution. The exceptions are the iteration indices. Moreover, if
the goal is of the form ` _Locals_^ _G_` all variables
occurring in  _Locals_ are marked as local. As an example:

~~~~~{.prolog}
foreach([I,J] ins 1..N, A^(A <==M[I,J], N[I] <== N[I] + A*A) )
~~~~~
the variables  _I_,  _J_ and  _A_ are duplicated for every
call (local), whereas the matrices  _M_ and  _N_ are shared
throughout the execution (global).

 
*/
EOF
sed -e "222r tmp" /Users/vsc/git/yap-6.3/library/dialect/bprolog/foreach.pl > x
     mv x /Users/vsc/git/yap-6.3/library/dialect/bprolog/foreach.pl

#true
cat << "EOF" > tmp
/** @pred foreach( _Sequence_,  _Goal_,  _Acc0_,  _AccF_)

Deterministic iterator with accumulator style arguments.

 
*/
EOF
sed -e "145r tmp" /Users/vsc/git/yap-6.3/library/dialect/bprolog/foreach.pl > x
     mv x /Users/vsc/git/yap-6.3/library/dialect/bprolog/foreach.pl

#false
cat << "EOF" > tmp
/** @pred  arg(+ _N_,+ _T_, _A_) is iso 


Succeeds if the argument  _N_ of the term  _T_ unifies with
 _A_. The arguments are numbered from 1 to the arity of the term.

The current version will generate an error if  _T_ or  _N_ are
unbound, if  _T_ is not a compound term, of if  _N_ is not a positive
integer. Note that previous versions of YAP would fail silently
under these errors.

 
*/
EOF
sed -e "163r tmp" /Users/vsc/git/yap-6.3/library/dialect/swi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dialect/swi.yap

#false
cat << "EOF" > tmp
/** @pred  atom_concat(? _A1_,? _A2_,? _A12_) is iso

The predicate holds when the third argument unifies with an atom, and
the first and second unify with atoms such that their representations
concatenated are the representation for  _A12_.

If  _A1_ and  _A2_ are unbound, the built-in will find all the atoms
that concatenated give  _A12_.

 
*/
EOF
sed -e "148r tmp" /Users/vsc/git/yap-6.3/library/dialect/swi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dialect/swi.yap

#false
cat << "EOF" > tmp
/** @pred concat_atom(? _List_,+ _Separator_,? _Atom_)


Creates an atom just like concat_atom/2, but inserts  _Separator_
between each pair of atoms.  For example:

~~~~~
?- concat_atom([gnu, gnat], ', ', A).

A = 'gnu, gnat'
~~~~~

(Unimplemented) This predicate can also be used to split atoms by
instantiating  _Separator_ and  _Atom_:

~~~~~
?- concat_atom(L, -, 'gnu-gnat').

L = [gnu, gnat]
~~~~~

 
*/
EOF
sed -e "42r tmp" /Users/vsc/git/yap-6.3/library/dialect/swi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dialect/swi.yap

#false
cat << "EOF" > tmp
/** @pred concat_atom(+ _List_,- _Atom_) 



 _List_ is a list of atoms, integers or floating point numbers. Succeeds
if  _Atom_ can be unified with the concatenated elements of  _List_. If
 _List_ has exactly 2 elements it is equivalent to `atom_concat/3`,
allowing for variables in the list.

 
*/
EOF
sed -e "42r tmp" /Users/vsc/git/yap-6.3/library/dialect/swi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dialect/swi.yap

#false
cat << "EOF" > tmp
/** @pred chdir(+ _Dir_) 



Compatibility predicate.  New code should use working_directory/2.

 
*/
EOF
sed -e "42r tmp" /Users/vsc/git/yap-6.3/library/dialect/swi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dialect/swi.yap

#true
cat << "EOF" > tmp
/** @pred  time_file(+ _File_,- _Time_) 


Unify the last modification time of  _File_ with
 _Time_.  _Time_ is a floating point number expressing the seconds
elapsed since Jan 1, 1970.

 
*/
EOF
sed -e "42r tmp" /Users/vsc/git/yap-6.3/library/dialect/swi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/dialect/swi.yap

#true
cat << "EOF" > tmp
/** @pred min(+ _Expression_)
Minimizes  _Expression_ within the current constraint store. This is
the same as computing the infimum and equation the expression to that
infimum.

 
*/
EOF
sed -e "75r tmp" /Users/vsc/git/yap-6.3/library/exo_interval.yap > x
     mv x /Users/vsc/git/yap-6.3/library/exo_interval.yap

#true
cat << "EOF" > tmp
/** @pred min( _X_,  _Vs_)
First Argument is the least element of a list.

 
*/
EOF
sed -e "75r tmp" /Users/vsc/git/yap-6.3/library/exo_interval.yap > x
     mv x /Users/vsc/git/yap-6.3/library/exo_interval.yap

#true
cat << "EOF" > tmp
/** @pred max(+ _Expression_)
Maximizes  _Expression_ within the current constraint store. This is
the same as computing the supremum and equating the expression to that
supremum.

 
*/
EOF
sed -e "75r tmp" /Users/vsc/git/yap-6.3/library/exo_interval.yap > x
     mv x /Users/vsc/git/yap-6.3/library/exo_interval.yap

#true
cat << "EOF" > tmp
/** @pred max( _X_,  _Vs_)
First Argument is the greatest element of a list.

+ lex_order( _Vs_)
All elements must be ordered.



The following predicates control search:

 
*/
EOF
sed -e "75r tmp" /Users/vsc/git/yap-6.3/library/exo_interval.yap > x
     mv x /Users/vsc/git/yap-6.3/library/exo_interval.yap

#false
cat << "EOF" > tmp
/** @pred min_of_heap(+ _Heap_,  - _Key_,  - _Datum_) 


Returns the Key-Datum pair at the top of the heap (which is of course
the pair with the smallest Key), but does not remove it from the heap.

 
*/
EOF
sed -e "131r tmp" /Users/vsc/git/yap-6.3/library/heaps.yap > x
     mv x /Users/vsc/git/yap-6.3/library/heaps.yap

#false
cat << "EOF" > tmp
/** @pred min_of_heap(+ _Heap_,  - _Key1_,  - _Datum1_,
- _Key2_,  - _Datum2_)

Returns the smallest (Key1) and second smallest (Key2) pairs in the
heap, without deleting them.



 */
EOF
sed -e "131r tmp" /Users/vsc/git/yap-6.3/library/heaps.yap > x
     mv x /Users/vsc/git/yap-6.3/library/heaps.yap

#false
cat << "EOF" > tmp
/** @pred list_to_heap(+ _List_, - _Heap_) 


Takes a list of  _Key-Datum_ pairs (such as keysort could be used to sort)
and forms them into a heap.

 
*/
EOF
sed -e "131r tmp" /Users/vsc/git/yap-6.3/library/heaps.yap > x
     mv x /Users/vsc/git/yap-6.3/library/heaps.yap

#false
cat << "EOF" > tmp
/** @pred heap_to_list(+ _Heap_, - _List_) 


Returns the current set of  _Key-Datum_ pairs in the  _Heap_ as a
 _List_, sorted into ascending order of  _Keys_.

 
*/
EOF
sed -e "131r tmp" /Users/vsc/git/yap-6.3/library/heaps.yap > x
     mv x /Users/vsc/git/yap-6.3/library/heaps.yap

#false
cat << "EOF" > tmp
/** @pred heap_size(+ _Heap_, - _Size_) 


Reports the number of elements currently in the heap.

 
*/
EOF
sed -e "131r tmp" /Users/vsc/git/yap-6.3/library/heaps.yap > x
     mv x /Users/vsc/git/yap-6.3/library/heaps.yap

#false
cat << "EOF" > tmp
/** @pred get_from_heap(+ _Heap_,- _key_,- _Datum_,- _Heap_) 


Returns the  _Key-Datum_ pair in  _OldHeap_ with the smallest
 _Key_, and also a  _Heap_ which is the  _OldHeap_ with that
pair deleted.

 
*/
EOF
sed -e "131r tmp" /Users/vsc/git/yap-6.3/library/heaps.yap > x
     mv x /Users/vsc/git/yap-6.3/library/heaps.yap

#false
cat << "EOF" > tmp
/** @pred empty_heap(? _Heap_) 


Succeeds if  _Heap_ is an empty heap.

 
*/
EOF
sed -e "131r tmp" /Users/vsc/git/yap-6.3/library/heaps.yap > x
     mv x /Users/vsc/git/yap-6.3/library/heaps.yap

#false
cat << "EOF" > tmp
/** @pred mpi_wait_recv(? _Handle_,- _Status_,- _Data_) 



Completes a non-blocking receive operation. The predicate blocks until
a message associated with handle  _Hanlde_ is buffered. The
predicate succeeds unifying  _Status_ with the status of the
message and  _Data_ with the message itself. 

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_wait(? _Handle_,- _Status_) 



Completes a non-blocking operation. If the operation was a
`mpi_send`, the predicate blocks until the message is buffered
or sent by the runtime system. At this point the send buffer is
released. If the operation was a `mpi_recv`, it waits until the
message is copied to the receive buffer.  _Status_ is unified with
the status of the message.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_version(- _Major_,- _Minor_) 


Unifies  _Major_ and  _Minor_ with, respectively, the major and minor version of the MPI.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_test_recv(? _Handle_,- _Status_,- _Data_) 



Provides information regarding a handle. If the message associated
with handle  _Hanlde_ is buffered then the predicate succeeds
unifying  _Status_ with the status of the message and  _Data_
with the message itself. Otherwise, the predicate fails.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_test(? _Handle_,- _Status_) 



Provides information regarding the handle  _Handle_, ie., if a
communication operation has been completed.  If the operation
associate with  _Hanlde_ has been completed the predicate succeeds
with the completion status in  _Status_, otherwise it fails.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#true
cat << "EOF" > tmp
/** @pred mpi_send(+ _Data_,+ _Dest_,+ _Tag_) 



Blocking communication predicate. The message in  _Data_, with tag
 _Tag_, is sent immediately to the processor with rank  _Dest_.
The predicate succeeds after the message being sent.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_recv(? _Source_,? _Tag_,- _Data_) 



Blocking communication predicate. The predicate blocks until a message
is received from processor with rank  _Source_ and tag  _Tag_.
The message is placed in  _Data_.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_msg_size( _Msg_, - _MsgSize_) 


Unify  _MsgSize_ with the number of bytes YAP would need to send the
message  _Msg_.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_isend(+ _Data_,+ _Dest_,+ _Tag_,- _Handle_) 



Non blocking communication predicate. The message in  _Data_, with
tag  _Tag_, is sent whenever possible to the processor with rank
 _Dest_. An  _Handle_ to the message is returned to be used to
check for the status of the message, using the `mpi_wait` or
`mpi_test` predicates. Until `mpi_wait` is called, the
memory allocated for the buffer containing the message is not
released.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_irecv(? _Source_,? _Tag_,- _Handle_) 



Non-blocking communication predicate. The predicate returns an
 _Handle_ for a message that will be received from processor with
rank  _Source_ and tag  _Tag_. Note that the predicate succeeds
immediately, even if no message has been received. The predicate
`mpi_wait_recv` should be used to obtain the data associated to
the handle.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_init 


Sets up the mpi environment. This predicate should be called before any other MPI predicate.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_gc 



Attempts to perform garbage collection with all the open handles
associated with send and non-blocking broadcasts. For each handle it
tests it and the message has been delivered the handle and the buffer
are released.




 */
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_finalize 


Terminates the MPI execution environment. Every process must call this predicate before  exiting.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_comm_size(- _Size_) 


Unifies  _Size_ with the number of processes in the MPI environment.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_comm_rank(- _Rank_) 


Unifies  _Rank_ with the rank of the current process in the MPI environment.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_bcast2(+ _Root_, ? _Data_) 



Broadcasts the message  _Data_ from the process with rank  _Root_
to all other processes.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#true
cat << "EOF" > tmp
/** @pred mpi_barrier 


Collective communication predicate.  Performs a barrier
synchronization among all processes. Note that a collective
communication means that all processes call the same predicate. To be
able to use a regular `mpi_recv` to receive the messages, one
should use `mpi_bcast2`.

 
*/
EOF
sed -e "188r tmp" /Users/vsc/git/yap-6.3/library/lam_mpi.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lam_mpi.yap

#false
cat << "EOF" > tmp
/** @pred mpi_default_buffer_size(- _OldBufferSize_, ? _NewBufferSize_) 



The  _OldBufferSize_ argument unifies with the current size of the
MPI communication buffer size and sets the communication buffer size
 _NewBufferSize_. The buffer is used for assynchronous waiting and
for broadcast receivers. Notice that buffer is local at each MPI
process.

 
*/
EOF
sed -e "1050r tmp" /Users/vsc/git/yap-6.3/library/lammpi/yap_mpi.c > x
     mv x /Users/vsc/git/yap-6.3/library/lammpi/yap_mpi.c

#false
cat << "EOF" > tmp
/** @pred mpi_ibcast(+ _Root_, + _Data_, + _Tag_) 



Non-blocking operation. Broadcasts the message  _Data_ with tag  _Tag_
from the process with rank  _Root_ to all other processes.

 
*/
EOF
sed -e "1038r tmp" /Users/vsc/git/yap-6.3/library/lammpi/yap_mpi.c > x
     mv x /Users/vsc/git/yap-6.3/library/lammpi/yap_mpi.c

#false
cat << "EOF" > tmp
/** @pred mpi_bcast3(+ _Root_, + _Data_, + _Tag_)


Broadcasts the message  _Data_ with tag  _Tag_ from the process with rank  _Root_
to all other processes.

 
*/
EOF
sed -e "1028r tmp" /Users/vsc/git/yap-6.3/library/lammpi/yap_mpi.c > x
     mv x /Users/vsc/git/yap-6.3/library/lammpi/yap_mpi.c

#false
cat << "EOF" > tmp
/** @pred split(+ _Line_,- _Split_)


Unify  _Words_ with a set of strings obtained from  _Line_ by
using the blank characters  as separators.

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#false
cat << "EOF" > tmp
/** @pred search_for(+ _Char_,+ _Line_,- _RestOfine_)


Search for a character  _Char_ in the list of codes  _Line_,
 _RestOfLine_ has the line to the right.

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#false
cat << "EOF" > tmp
/** @pred scan_natural(? _Nat_,+ _Line_,+ _RestOfLine_) 



Scan the list of codes  _Line_ for a natural number  _Nat_, zero
or a positive integer, and unify  _RestOfLine_ with the remainder
of the line.

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#false
cat << "EOF" > tmp
/** @pred scan_integer(? _Int_,+ _Line_,+ _RestOfLine_) 



Scan the list of codes  _Line_ for an integer  _Nat_, either a
positive, zero, or negative integer, and unify  _RestOfLine_ with
the remainder of the line.

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#false
cat << "EOF" > tmp
/** @pred glue(+ _Words_,+ _Separator_,- _Line_) 



Unify  _Line_ with  string obtained by glueing  _Words_ with
the character code  _Separator_.

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#false
cat << "EOF" > tmp
/** @pred filter(+ _StreamInp_, + _StreamOut_, + _Goal_) 



For every line  _LineIn_ in stream  _StreamInp_, execute
`call(Goal,LineIn,LineOut)`, and output  _LineOut_ to
stream  _StreamOut_.

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#false
cat << "EOF" > tmp
/** @pred file_filter_with_initialization(+ _FileIn_, + _FileOut_, + _Goal_, + _FormatCommand_,   + _Arguments_)


Same as file_filter/3, but before starting the filter execute
`format/3` on the output stream, using  _FormatCommand_ and
 _Arguments_.




 */
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#false
cat << "EOF" > tmp
/** @pred file_filter(+ _FileIn_, + _FileOut_, + _Goal_) 



For every line  _LineIn_ in file  _FileIn_, execute
`call(Goal,LineIn,LineOut)`, and output  _LineOut_ to file
 _FileOut_.

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#false
cat << "EOF" > tmp
/** @pred fields(+ _Line_,- _Split_)


Unify  _Words_ with a set of strings obtained from  _Line_ by
using the blank characters  as field separators.

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#true
cat << "EOF" > tmp
/** @pred fields(+ _Line_,+ _Separators_,- _Split_) 



Unify  _Words_ with a set of strings obtained from  _Line_ by
using the character codes in  _Separators_ as separators for
fields. If two separators occur in a row, the field is considered
empty. As an example, consider:

~~~~~{.prolog}
?- fields("Hello  I am  free"," *",S).

S = ["Hello","","I","am","","free"] ?
~~~~~

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#true
cat << "EOF" > tmp
/** @pred copy_line(+ _StreamInput_,+ _StreamOutput_) 



Copy a line from  _StreamInput_ to  _StreamOutput_.

 
*/
EOF
sed -e "1r tmp" /Users/vsc/git/yap-6.3/library/lineutils.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lineutils.yap

#true
cat << "EOF" > tmp
/** @pred sumlist(? _Numbers_, ? _Total_) 


True when  _Numbers_ is a list of integers, and  _Total_ is their
sum. The same as sum_list/2, please do use sum_list/2
instead.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#false
cat << "EOF" > tmp
/** @pred sum_list(? _Numbers_, ? _Total_) 


True when  _Numbers_ is a list of numbers, and  _Total_ is their sum.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#false
cat << "EOF" > tmp
/** @pred sum_list(? _Numbers_, + _SoFar_, ? _Total_)

True when  _Numbers_ is a list of numbers, and  _Total_ is the sum of their total plus  _SoFar_.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#false
cat << "EOF" > tmp
/** @pred suffix(? _Suffix_, ? _List_) 


Holds when `append(_,Suffix,List)` holds.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred subtract(+ _Set_, + _Delete_, ? _Result_) 


Delete all elements from  _Set_ that   occur  in  _Delete_ (a set)
and unify the  result  with   _Result_.   Deletion  is  based  on
unification using memberchk/2. The complexity is
`|Delete|\*|Set|`.

See ord_subtract/3.



 */
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred sublist(? _Sublist_, ? _List_) 


True when both `append(_,Sublist,S)` and `append(S,_,List)` hold.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred selectchk(? _Element_, ? _List_, ? _Residue_) 


Semi-deterministic selection from a list. Steadfast: defines as

~~~~~{.prolog}
selectchk(Elem, List, Residue) :-
        select(Elem, List, Rest0), !,
        Rest = Rest0.
~~~~~

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred select(? _Element_, ? _List_, ? _Residue_) 


True when  _Set_ is a list,  _Element_ occurs in  _List_, and
 _Residue_ is everything in  _List_ except  _Element_ (things
stay in the same order).

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#false
cat << "EOF" > tmp
/** @pred same_length(? _List1_, ? _List2_) 


True when  _List1_ and  _List2_ are both lists and have the same number
of elements.  No relation between the values of their elements is
implied.
Modes `same_length(-,+)` and `same_length(+,-)` generate either list given
the other; mode `same_length(-,-)` generates two lists of the same length,
in which case the arguments will be bound to lists of length 0, 1, 2, ...

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#false
cat << "EOF" > tmp
/** @pred remove_duplicates(+ _List_, ? _Pruned_) 


Removes duplicated elements from  _List_.  Beware: if the  _List_ has
non-ground elements, the result may surprise you.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred permutation(+ _List_,? _Perm_) 


True when  _List_ and  _Perm_ are permutations of each other.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#false
cat << "EOF" > tmp
/** @pred numlist(+ _Low_, + _High_, + _List_) 


If  _Low_ and  _High_ are integers with  _Low_ =<
 _High_, unify  _List_ to a list `[Low, Low+1, ...High]`. See
also between/3.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred nth1(? _N_, ? _List_, ? _Elem_, ? _Rest_)

Unifies  _Elem_ with the Nth element of  _List_, counting from 1,
and  _Rest_ with the other elements.  It can be used to select the
Nth element of  _List_ (yielding  _Elem_ and  _Rest_), or to
insert  _Elem_ before the Nth (counting from 1) element of
 _Rest_, when it yields  _List_, e.g. `nth(3, List, c, [a,b,d,e])` unifies List with `[a,b,c,d,e]`.  `nth/4`
can be used to insert  _Elem_ after the Nth element of  _Rest_.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred nth1(? _N_, ? _List_, ? _Elem_) 


The same as nth0/3, except that it counts from
1, that is `nth(1, [H|_], H)`.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred nth1(+ _Index_,? _List_,? _Elem_) 


Succeeds when the  _Index_-th element of  _List_ unifies with
 _Elem_. Counting starts at 1.

Set environment variable.   _Name_ and  _Value_ should be
instantiated to atoms or integers.  The environment variable will be
passed to `shell/[0-2]` and can be requested using `getenv/2`.
They also influence expand_file_name/2.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred nth0(? _N_, ? _List_, ? _Elem_, ? _Rest_)

Unifies  _Elem_ with the Nth element of  _List_,
counting from 0, and  _Rest_ with the other elements.  It can be used
to select the Nth element of  _List_ (yielding  _Elem_ and  _Rest_), or to
insert  _Elem_ before the Nth (counting from 1) element of  _Rest_, when
it yields  _List_, e.g. `nth0(2, List, c, [a,b,d,e])` unifies List with
`[a,b,c,d,e]`.  `nth/4` is the same except that it counts from 1.  `nth0/4`
can be used to insert  _Elem_ after the Nth element of  _Rest_.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred nth0(? _N_, ? _List_, ? _Elem_) 


True when  _Elem_ is the Nth member of  _List_,
counting the first as element 0.  (That is, throw away the first
N elements and unify  _Elem_ with the next.)  It can only be used to
select a particular element given the list and index.  For that
task it is more efficient than member/2

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#false
cat << "EOF" > tmp
/** @pred nth(? _N_, ? _List_, ? _Elem_, ? _Rest_)

Same as `nth1/4`.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#false
cat << "EOF" > tmp
/** @pred nth(? _N_, ? _List_, ? _Elem_) 


The same as nth1/3.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred min_list(? _Numbers_, ? _Min_) 


True when  _Numbers_ is a list of numbers, and  _Min_ is the minimum.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred max_list(? _Numbers_, ? _Max_) 


True when  _Numbers_ is a list of numbers, and  _Max_ is the maximum.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#false
cat << "EOF" > tmp
/** @pred list_concat(+ _Lists_,? _List_) 


True when  _Lists_ is a list of lists and  _List_ is the
concatenation of  _Lists_.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred last(+ _List_,? _Last_) 


True when  _List_ is a list and  _Last_ is identical to its last element.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred intersection(+ _Set1_, + _Set2_, + _Set3_) 


Succeeds if  _Set3_ unifies with the intersection of  _Set1_ and
 _Set2_.  _Set1_ and  _Set2_ are lists without duplicates. They
need not be ordered.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred flatten(+ _List_, ? _FlattenedList_) 


Flatten a list of lists  _List_ into a single list
 _FlattenedList_.

~~~~~{.prolog}
?- flatten([[1],[2,3],[4,[5,6],7,8]],L).

L = [1,2,3,4,5,6,7,8] ? ;

no
~~~~~

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred append(? _Lists_,? _Combined_)

Holds if the lists of  _Lists_ can be concatenated as a
 _Combined_ list.

 
*/
EOF
sed -e "261r tmp" /Users/vsc/git/yap-6.3/library/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/library/lists.yap

#true
cat << "EOF" > tmp
/** @pred maplist(+ _Pred_,+ _List1_,+ _List2_,+ _List4_)

Apply  _Pred_ on all successive triples of elements from  _List1_,
 _List2_ and  _List3_. Fails if  _Pred_ can not be applied to a
triple. See the example above.




 */
EOF
sed -e "98r tmp" /Users/vsc/git/yap-6.3/library/maplist.yap > x
     mv x /Users/vsc/git/yap-6.3/library/maplist.yap

#true
cat << "EOF" > tmp
/** @pred maplist(+ _Pred_,+ _List1_,+ _List2_)

Apply  _Pred_ on all successive pairs of elements from
 _List1_ and
 _List2_. Fails if  _Pred_ can not be applied to a
pair. See the example above.

 
*/
EOF
sed -e "98r tmp" /Users/vsc/git/yap-6.3/library/maplist.yap > x
     mv x /Users/vsc/git/yap-6.3/library/maplist.yap

#false
cat << "EOF" > tmp
/** @pred matlab_zeros(+ _Size_, ? _Array_) 


MATLAB will create a vector of zeros of size  _Size_, and if
 _Array_ is bound to an atom, store the array in the matlab
variable with name  _Array_. Corresponds to the MATLAB command
`zeros`.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_zeros(+ _SizeX_, + _SizeY_, ? _Array_)

MATLAB will create an array of zeros of size  _SizeX_ and
 _SizeY_, and if  _Array_ is bound to an atom, store the array
in the matlab variable with name  _Array_.  Corresponds to the
MATLAB command `zeros`.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_zeros(+ _SizeX_, + _SizeY_, + _SizeZ_, ? _Array_)

MATLAB will create an array of zeros of size  _SizeX_,  _SizeY_,
and  _SizeZ_. If  _Array_ is bound to an atom, store the array
in the matlab variable with name  _Array_.  Corresponds to the
MATLAB command `zeros`.




 */
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_vector(+ _Size_, + _List_, ? _Array_) 


MATLAB will create a vector of floats of size  _Size_, initialized
from the list  _List_, and if  _Array_ is bound to an atom,
store the array in the matlab variable with name  _Array_.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_set(+ _MatVar_, + _X_, + _Y_, + _Value_) 


Call MATLAB to set element  _MatVar_( _X_,  _Y_) to
 _Value_. Notice that this command uses the MATLAB array access
convention.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_sequence(+ _Min_, + _Max_, ? _Array_) 


MATLAB will create a sequence going from  _Min_ to  _Max_, and
if  _Array_ is bound to an atom, store the sequence in the matlab
variable with name  _Array_.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_on 


Holds if a matlab session is on.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_matrix(+ _SizeX_, + _SizeY_, + _List_, ? _Array_) 


MATLAB will create an array of floats of size  _SizeX_ and  _SizeY_,
initialized from the list  _List_, and if  _Array_ is bound to
an atom, store the array in the matlab variable with name  _Array_.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_item1(+ _MatVar_, + _X_, ? _Val_) 


Read or set MATLAB  _MatVar_( _X_) from/to  _Val_. Use
MATLAB notation for matrix access (ie, starting from 1).

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_item1(+ _MatVar_, + _X_, + _Y_, ? _Val_)

Read or set MATLAB  _MatVar_( _X_, _Y_) from/to  _Val_. Use
MATLAB notation for matrix access (ie, starting from 1).

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_item(+ _MatVar_, + _X_, ? _Val_) 


Read or set MATLAB  _MatVar_( _X_) from/to  _Val_. Use
`C` notation for matrix access (ie, starting from 0).

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_item(+ _MatVar_, + _X_, + _Y_, ? _Val_)

Read or set MATLAB  _MatVar_( _X_, _Y_) from/to  _Val_. Use
`C` notation for matrix access (ie, starting from 0).

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_initialized_cells(+ _SizeX_, + _SizeY_, + _List_, ? _Array_) 


MATLAB will create an array of cells of size  _SizeX_ and
 _SizeY_, initialized from the list  _List_, and if  _Array_
is bound to an atom, store the array in the matlab variable with name
 _Array_.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_get_variable(+ _MatVar_, - _List_) 


Unify MATLAB variable  _MatVar_ with the List  _List_.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_eval_string(+ _Command_, - _Answer_)

MATLAB will evaluate the command  _Command_ and unify  _Answer_
with a string reporting the result.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_eval_string(+ _Command_) 


Holds if matlab evaluated successfully the command  _Command_.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_cells(+ _Size_, ? _Array_) 


MATLAB will create an empty vector of cells of size  _Size_, and if
 _Array_ is bound to an atom, store the array in the matlab
variable with name  _Array_. Corresponds to the MATLAB command `cells`.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matlab_cells(+ _SizeX_, + _SizeY_, ? _Array_)

MATLAB will create an empty array of cells of size  _SizeX_ and
 _SizeY_, and if  _Array_ is bound to an atom, store the array
in the matlab variable with name  _Array_.  Corresponds to the
MATLAB command `cells`.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred close_matlab 


Stop the current matlab session.

 
*/
EOF
sed -e "192r tmp" /Users/vsc/git/yap-6.3/library/matlab.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matlab.yap

#false
cat << "EOF" > tmp
/** @pred matrix_type(+ _Matrix_,- _Type_) 



Unify  _NElems_ with the type of the elements in  _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_transpose(+ _Matrix_,- _Transpose_) 



Transpose matrix  _Matrix_ to   _Transpose_. Equivalent to:

~~~~~
matrix_transpose(Matrix,Transpose) :-
        matrix_shuffle(Matrix,[1,0],Transpose).
~~~~~

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_to_list(+ _Matrix_,- _Elems_) 



Unify  _Elems_ with the list including all the elements in  _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_sum(+ _Matrix_,+ _Sum_) 



Unify  _Sum_ with the sum of all elements in matrix   _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_size(+ _Matrix_,- _NElems_) 



Unify  _NElems_ with the number of elements for  _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_shuffle(+ _Matrix_,+ _NewOrder_,- _Shuffle_) 



Shuffle the dimensions of matrix  _Matrix_ according to
 _NewOrder_. The list  _NewOrder_ must have all the dimensions of
 _Matrix_, starting from 0.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_set_all(+ _Matrix_,+ _Elem_) 



Set all element of  _Matrix_ to  _Elem_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_set(+ _Matrix_[+ _Position_],+ _Elem_)


Set the element of  _Matrix_[ _Position_] to   _Elem_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_set(+ _Matrix_,+ _Position_,+ _Elem_) 



Set the element of  _Matrix_ at position
 _Position_ to   _Elem_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_select(+ _Matrix_,+ _Dimension_,+ _Index_,- _New_) 



Select from  _Matrix_ the elements who have  _Index_ at
 _Dimension_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_op_to_lines(+ _Matrix1_,+ _Lines_,+ _Op_,- _Result_) 



 _Result_ is the result of applying  _Op_ to all elements of
 _Matrix1_, with the corresponding element in  _Lines_ as the
second argument. Currently, only division (`/`) is supported.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_op_to_cols(+ _Matrix1_,+ _Cols_,+ _Op_,- _Result_) 



 _Result_ is the result of applying  _Op_ to all elements of
 _Matrix1_, with the corresponding element in  _Cols_ as the
second argument. Currently, only addition (`+`) is
supported. Notice that  _Cols_ will have n-1 dimensions.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_op_to_all(+ _Matrix1_,+ _Op_,+ _Operand_,- _Result_) 



 _Result_ is the result of applying  _Op_ to all elements of
 _Matrix1_, with  _Operand_ as the second argument. Currently,
only addition (`+`), multiplication (`\*`), and division
(`/`) are supported.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_op(+ _Matrix1_,+ _Matrix2_,+ _Op_,- _Result_) 



 _Result_ is the result of applying  _Op_ to matrix  _Matrix1_
and  _Matrix2_. Currently, only addition (`+`) is supported.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_offset_to_arg(+ _Matrix_,- _Offset_,+ _Position_) 



Given a position  _Position _ for matrix  _Matrix_ return the
corresponding numerical  _Offset_ from the beginning of the matrix.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_new_set(? _Dims_,+ _OldMatrix_,+ _Value_,- _NewMatrix_) 



Create a new matrix  _NewMatrix_ of type  _Type_, with dimensions
 _Dims_. The elements of  _NewMatrix_ are set to  _Value_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_new(+ _Type_,+ _Dims_,- _Matrix_) 



Create a new matrix  _Matrix_ of type  _Type_, which may be one of
`ints` or `floats`, and with a list of dimensions  _Dims_.
The matrix will be initialised to zeros.

~~~~~
?- matrix_new(ints,[2,3],Matrix).

Matrix = {..}
~~~~~
Notice that currently YAP will always write a matrix of numbers as `{..}`.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_new(+ _Type_,+ _Dims_,+ _List_,- _Matrix_)


Create a new matrix  _Matrix_ of type  _Type_, which may be one of
`ints` or `floats`, with dimensions  _Dims_, and
initialised from list  _List_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_ndims(+ _Matrix_,- _Dims_) 



Unify  _NDims_ with the number of dimensions for  _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_minarg(+ _Matrix_,+ _Minarg_) 



Unify  _Min_ with the position of the minimum in matrix   _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_min(+ _Matrix_,+ _Min_) 



Unify  _Min_ with the minimum in matrix   _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_maxarg(+ _Matrix_,+ _Maxarg_) 



Unify  _Max_ with the position of the maximum in matrix   _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_max(+ _Matrix_,+ _Max_) 



Unify  _Max_ with the maximum in matrix   _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_inc(+ _Matrix_,+ _Position_,- _Element_)


Increment the element of  _Matrix_ at position  _Position_ and
unify with  _Element_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_inc(+ _Matrix_,+ _Position_) 



Increment the element of  _Matrix_ at position  _Position_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_get(+ _Matrix_[+ _Position_],- _Elem_)


Unify  _Elem_ with the element  _Matrix_[ _Position_].

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_get(+ _Matrix_,+ _Position_,- _Elem_) 



Unify  _Elem_ with the element of  _Matrix_ at position
 _Position_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_expand(+ _Matrix_,+ _NewDimensions_,- _New_) 



Expand  _Matrix_ to occupy new dimensions. The elements in
 _NewDimensions_ are either 0, for an existing dimension, or a
positive integer with the size of the new dimension.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_dims(+ _Matrix_,- _Dims_) 



Unify  _Dims_ with a list of dimensions for  _Matrix_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_dec(+ _Matrix_,+ _Position_,- _Element_)


Decrement the element of  _Matrix_ at position  _Position_ and
unify with  _Element_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_dec(+ _Matrix_,+ _Position_) 



Decrement the element of  _Matrix_ at position  _Position_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_column(+ _Matrix_,+ _Column_,- _NewMatrix_) 



Select from  _Matrix_ the column matching  _Column_ as new matrix  _NewMatrix_.  _Column_ must have one less dimension than the original matrix.



 */
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_arg_to_offset(+ _Matrix_,+ _Position_,- _Offset_) 



Given matrix  _Matrix_ return what is the numerical  _Offset_ of
the element at  _Position_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_agg_lines(+ _Matrix_,+Operator,+ _Aggregate_) 



If  _Matrix_ is a n-dimensional matrix, unify  _Aggregate_ with
the n-1 dimensional matrix where each element is obtained by adding all
_Matrix_ elements with same last n-1 index. Currently, only addition is supported.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_agg_cols(+ _Matrix_,+Operator,+ _Aggregate_) 



If  _Matrix_ is a n-dimensional matrix, unify  _Aggregate_ with
the one dimensional matrix where each element is obtained by adding all
Matrix elements with same  first index. Currently, only addition is supported.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#false
cat << "EOF" > tmp
/** @pred matrix_add(+ _Matrix_,+ _Position_,+ _Operand_) 



Add  _Operand_ to the element of  _Matrix_ at position
 _Position_.

 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#true
cat << "EOF" > tmp
/** @pred ?_LHS_ <==  ?_RHS_ is semidet


General matrix assignment operation. It evaluates the right-hand side
and then acts different according to the
left-hand side and to the matrix:

+ if  _LHS_ is part of an integer or floating-point matrix,
perform non-backtrackable assignment.
+ other unify left-hand side and right-hand size.


The right-hand side supports the following operators: 

+ `[]/2`

    written as  _M_[ _Offset_]: obtain an element or list of elements
of matrix  _M_ at offset  _Offset_.

+ `matrix/1`

    create a vector from a list

+ `matrix/2`

    create a matrix from a list. Options are:
  + dim=
a list of dimensions
  + type=
integers, floating-point or terms
  + base=
a list of base offsets per dimension (all must be the same for arrays of
integers and floating-points

+ `matrix/3`

    create matrix giving two options

  + `dim/1`
  list with matrix dimensions

  + `nrow/1`
  number of rows in bi-dimensional matrix

+ `ncol/1`
  number of columns in bi-dimensional matrix

+ `length/1`
  size of a matrix

+ `size/1`
  size of a matrix

+ `max/1`
  
    maximum element of a numeric matrix

+ `maxarg/1`
  
    argument of maximum element of a numeric matrix

+ `min/1`
  
    minimum element of a numeric matrix

+ `minarg/1`
  
    argument of minimum element of a numeric matrix

+ `list/1`
  
    represent matrix as a list

+ `lists/2`
  
    represent matrix as list of embedded lists

+ `../2`
  
    _I_.. _J_ generates a list with all integers from  _I_ to
 _J_, included.

+ `+/2`
  
    add two numbers, add two matrices element-by-element, or add a number to
all elements of a matrix or list.

+ `-/2 `

    subtract two numbers, subtract two matrices or lists element-by-element, or subtract a number from
all elements of a matrix or list

+ `* /2`

    multiply two numbers, multiply two matrices or lists element-by-element, or multiply a number from
all elements of a matrix or list

 + `log/1`
 
    natural logarithm of a number, matrix or list

+ `exp/1 `

    natural exponentiation of a number, matrix or list
 
*/
EOF
sed -e "571r tmp" /Users/vsc/git/yap-6.3/library/matrix.yap > x
     mv x /Users/vsc/git/yap-6.3/library/matrix.yap

#true
cat << "EOF" > tmp
/** @pred nb_queue_size(+ _Queue_, - _Size_) 


Unify  _Size_ with the number of elements in the queue   _Queue_.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_queue_peek(+ _Queue_, - _Element_) 


 _Element_ is the front of the queue   _Queue_. Fail if
the queue is empty.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_queue_enqueue(+ _Queue_, + _Element_) 


Add  _Element_ to the front of the queue   _Queue_.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_queue_empty(+ _Queue_) 


Succeeds if   _Queue_ is empty.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_queue_dequeue(+ _Queue_, - _Element_) 


Remove  _Element_ from the front of the queue   _Queue_. Fail if
the queue is empty.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_queue_close(+ _Queue_, - _Head_, ? _Tail_) 


Unify the queue   _Queue_ with a difference list
 _Head_- _Tail_. The queue will now be empty and no further
elements can be added.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_queue(- _Queue_) 


Create a  _Queue_.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_heap_size(+ _Heap_, - _Size_) 


Unify  _Size_ with the number of elements in the heap   _Heap_.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_heap_peek(+ _Heap_, - _Key_, - _Value_)) 


 _Key_- _Value_ is the element with smallest  _Key_ in the heap
 _Heap_. Fail if the heap is empty.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_heap_empty(+ _Heap_) 


Succeeds if   _Heap_ is empty.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_heap_del(+ _Heap_, - _Key_, - _Value_) 


Remove element  _Key_- _Value_ with smallest  _Value_ in heap
 _Heap_. Fail if the heap is empty.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_heap_close(+ _Heap_) 


Close the heap  _Heap_: no further elements can be added.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_heap_add(+ _Heap_, + _Key_, + _Value_) 


Add  _Key_- _Value_ to the heap  _Heap_. The key is sorted on
 _Key_ only.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_heap(+ _DefaultSize_,- _Heap_) 


Create a  _Heap_ with default size  _DefaultSize_. Note that size
will expand as needed.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_beam_size(+ _Beam_, - _Size_) 


Unify  _Size_ with the number of elements in the beam   _Beam_.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_beam_peek(+ _Beam_, - _Key_, - _Value_)) 


 _Key_- _Value_ is the element with smallest  _Key_ in the beam
 _Beam_. Fail if the beam is empty.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_beam_empty(+ _Beam_) 


Succeeds if   _Beam_ is empty.




 */
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_beam_del(+ _Beam_, - _Key_, - _Value_) 


Remove element  _Key_- _Value_ with smallest  _Value_ in beam
 _Beam_. Fail if the beam is empty.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_beam_close(+ _Beam_) 


Close the beam  _Beam_: no further elements can be added.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_beam_add(+ _Beam_, + _Key_, + _Value_) 


Add  _Key_- _Value_ to the beam  _Beam_. The key is sorted on
 _Key_ only.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#true
cat << "EOF" > tmp
/** @pred nb_beam(+ _DefaultSize_,- _Beam_) 


Create a  _Beam_ with default size  _DefaultSize_. Note that size
is fixed throughout.

 
*/
EOF
sed -e "190r tmp" /Users/vsc/git/yap-6.3/library/nb.yap > x
     mv x /Users/vsc/git/yap-6.3/library/nb.yap

#false
cat << "EOF" > tmp
/** @pred ord_union(+ _Sets_, ? _Union_) 


Holds when  _Union_ is the union of the lists  _Sets_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_union(+ _Set1_, + _Set2_, ? _Union_, ? _Diff_)

Holds when  _Union_ is the union of  _Set1_ and  _Set2_ and
 _Diff_ is the difference.




 */
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_union(+ _Set1_, + _Set2_, ? _Union_)

Holds when  _Union_ is the union of  _Set1_ and  _Set2_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_symdiff(+ _Set1_, + _Set2_, ? _Difference_) 


Holds when  _Difference_ is the symmetric difference of  _Set1_
and  _Set2_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_subtract(+ _Set1_, + _Set2_, ? _Difference_) 


Holds when  _Difference_ contains all and only the elements of  _Set1_
which are not also in  _Set2_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_subset(+ _Set1_, + _Set2_) 


Holds when every element of the ordered set  _Set1_ appears in the
ordered set  _Set2_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_setproduct(+ _Set1_, + _Set2_, - _Set_) 


If Set1 and Set2 are ordered sets, Product will be an ordered
set of x1-x2 pairs.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_seteq(+ _Set1_, + _Set2_) 


Holds when the two arguments represent the same set.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_member(+ _Element_, + _Set_) 


Holds when  _Element_ is a member of  _Set_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_intersection(+ _Set1_, + _Set2_, ? _Intersection_, ? _Diff_)

Holds when Intersection is the ordered representation of  _Set1_
and  _Set2_.  _Diff_ is the difference between  _Set2_ and  _Set1_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_intersection(+ _Set1_, + _Set2_, ? _Intersection_)

Holds when Intersection is the ordered representation of  _Set1_
and  _Set2_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_intersect(+ _Set1_, + _Set2_) 


Holds when the two ordered sets have at least one element in common.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_insert(+ _Set1_, + _Element_, ? _Set2_) 


Inserting  _Element_ in  _Set1_ returns  _Set2_.  It should give
exactly the same result as `merge(Set1, [Element], Set2)`, but a
bit faster, and certainly more clearly. The same as ord_add_element/3.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_disjoint(+ _Set1_, + _Set2_) 


Holds when the two ordered sets have no element in common.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_del_element(+ _Set1_, + _Element_, ? _Set2_) 


Removing  _Element_ from  _Set1_ returns  _Set2_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ord_add_element(+ _Set1_, + _Element_, ? _Set2_) 


Inserting  _Element_ in  _Set1_ returns  _Set2_.  It should give
exactly the same result as `merge(Set1, [Element], Set2)`, but a
bit faster, and certainly more clearly. The same as ord_insert/3.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#true
cat << "EOF" > tmp
/** @pred merge(+ _List1_, + _List2_, - _Merged_) 


Holds when  _Merged_ is the stable merge of the two given lists.

Notice that merge/3 will not remove duplicates, so merging
ordered sets will not necessarily result in an ordered set. Use
`ord_union/3` instead.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred list_to_ord_set(+ _List_, ? _Set_) 


Holds when  _Set_ is the ordered representation of the set
represented by the unordered representation  _List_.

 
*/
EOF
sed -e "175r tmp" /Users/vsc/git/yap-6.3/library/ordsets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ordsets.yap

#false
cat << "EOF" > tmp
/** @pred ranunif(+ _Range_,- _I_) 


ranunif/2 produces a uniformly distributed non-negative random
integer  _I_ over a caller-specified range  _R_.  If range is  _R_,
the result is in 0 ..  _R_-1.




 */
EOF
sed -e "91r tmp" /Users/vsc/git/yap-6.3/library/prandom.yap > x
     mv x /Users/vsc/git/yap-6.3/library/prandom.yap

#false
cat << "EOF" > tmp
/** @pred ranstart(+ _Seed_)

Initialize the random number generator with user-defined  _Seed_. The
same  _Seed_ always produces the same sequence of numbers.

 
*/
EOF
sed -e "91r tmp" /Users/vsc/git/yap-6.3/library/prandom.yap > x
     mv x /Users/vsc/git/yap-6.3/library/prandom.yap

#false
cat << "EOF" > tmp
/** @pred ranstart 


Initialize the random number generator using a built-in seed. The
ranstart/0 built-in is always called by the system when loading
the package.

 
*/
EOF
sed -e "91r tmp" /Users/vsc/git/yap-6.3/library/prandom.yap > x
     mv x /Users/vsc/git/yap-6.3/library/prandom.yap

#false
cat << "EOF" > tmp
/** @pred rannum(- _I_) 


Produces a random non-negative integer  _I_ whose low bits are not
all that random, so it should be scaled to a smaller range in general.
The integer  _I_ is in the range 0 .. 2^(w-1) - 1. You can use:

~~~~~
rannum(X) :- yap_flag(max_integer,MI), rannum(R), X is R/MI.
~~~~~
to obtain a floating point number uniformly distributed between 0 and 1.

 
*/
EOF
sed -e "91r tmp" /Users/vsc/git/yap-6.3/library/prandom.yap > x
     mv x /Users/vsc/git/yap-6.3/library/prandom.yap

#false
cat << "EOF" > tmp
/** @pred serve_queue(+ _OldQueue_, + _Head_, - _NewQueue_) 


Removes the first element of the queue for service.

 
*/
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred queue_to_list(+ _Queue_, - _List_) 


Creates a new list with the same elements as  _Queue_.




 */
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred list_to_queue(+ _List_, - _Queue_) 


Creates a new queue with the same elements as  _List._

 
*/
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred list_jump_queue(+ _List_, + _OldQueue_, + _NewQueue_) 


Adds all the elements of  _List_ at the front of the queue.

 
*/
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred list_join_queue(+ _List_, + _OldQueue_, - _NewQueue_) 


Ads the new elements at the end of the queue.

 
*/
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred length_queue(+ _Queue_, - _Length_) 


Counts the number of elements currently in the queue.

 
*/
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred jump_queue(+ _Element_, + _OldQueue_, - _NewQueue_) 


Adds the new element at the front of the list.

 
*/
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred join_queue(+ _Element_, + _OldQueue_, - _NewQueue_) 


Adds the new element at the end of the queue.

 
*/
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred head_queue(+ _Queue_, ? _Head_) 


Unifies Head with the first element of the queue.

 
*/
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred empty_queue(+ _Queue_) 


Tests whether the queue is empty.

 
*/
EOF
sed -e "101r tmp" /Users/vsc/git/yap-6.3/library/queues.yap > x
     mv x /Users/vsc/git/yap-6.3/library/queues.yap

#false
cat << "EOF" > tmp
/** @pred setrand(+ _Key_) 


Use a term of the form `rand(X,Y,Z)` to set a new state for the
random number generator. The integer `X` must be in the range
`[1...30269)`, the integer `Y` must be in the range
`[1...30307)`, and the integer `Z` must be in the range
`[1...30323)`.




 */
EOF
sed -e "106r tmp" /Users/vsc/git/yap-6.3/library/random.yap > x
     mv x /Users/vsc/git/yap-6.3/library/random.yap

#false
cat << "EOF" > tmp
/** @pred randset(+ _LENGTH_, + _MAX_, - _Numbers_) 


Unify  _Numbers_ with an ordered list of  _LENGTH_ unique random
integers in the range `[1... _MAX_)`.

 
*/
EOF
sed -e "106r tmp" /Users/vsc/git/yap-6.3/library/random.yap > x
     mv x /Users/vsc/git/yap-6.3/library/random.yap

#false
cat << "EOF" > tmp
/** @pred randseq(+ _LENGTH_, + _MAX_, - _Numbers_) 


Unify  _Numbers_ with a list of  _LENGTH_ unique random integers
in the range `[1... _MAX_)`.

 
*/
EOF
sed -e "106r tmp" /Users/vsc/git/yap-6.3/library/random.yap > x
     mv x /Users/vsc/git/yap-6.3/library/random.yap

#false
cat << "EOF" > tmp
/** @pred random(- _Number_) 


Unify  _Number_ with a floating-point number in the range `[0...1)`.

 
*/
EOF
sed -e "106r tmp" /Users/vsc/git/yap-6.3/library/random.yap > x
     mv x /Users/vsc/git/yap-6.3/library/random.yap

#false
cat << "EOF" > tmp
/** @pred random(+ _LOW_, + _HIGH_, - _NUMBER_)

Unify  _Number_ with a number in the range
`[LOW...HIGH)`. If both  _LOW_ and  _HIGH_ are
integers then  _NUMBER_ will also be an integer, otherwise
 _NUMBER_ will be a floating-point number.

 
*/
EOF
sed -e "106r tmp" /Users/vsc/git/yap-6.3/library/random.yap > x
     mv x /Users/vsc/git/yap-6.3/library/random.yap

#false
cat << "EOF" > tmp
/** @pred rb_visit(+ _T_,- _Pairs_) 


 _Pairs_ is an infix visit of tree  _T_, where each element of
 _Pairs_ is of the form   _K_- _Val_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_update(+ _T_,+ _Key_,+ _NewVal_,- _TN_) 


Tree  _TN_ is tree  _T_, but with value for  _Key_ associated
with  _NewVal_. Fails if it cannot find  _Key_ in  _T_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_size(+ _T_,- _Size_) 


 _Size_ is the number of elements in  _T_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_previous(+ _T_, + _Key_,- _Previous_,- _Value_) 


 _Previous_ is the previous element after  _Key_ in  _T_, and is
associated with  _Val_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_partial_map(+ _T_,+ _Keys_,+ _G_,- _TN_) 


For all nodes  _Key_ in  _Keys_, if the value associated with key
 _Key_ is  _Val0_ in tree  _T_, and if `call(G,Val0,ValF)`
holds, then the value associated with  _Key_ in  _TN_ is
 _ValF_. Fails if or if `call(G,Val0,ValF)` is not satisfiable
for all  _Var0_. Assumes keys are not repeated.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_next(+ _T_, + _Key_,- _Next_,- _Value_) 


 _Next_ is the next element after  _Key_ in  _T_, and is
associated with  _Val_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_new(? _T_) 


Create a new tree.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_min(+ _T_,- _Key_,- _Value_) 


 _Key_  is the minimum key in  _T_, and is associated with  _Val_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_max(+ _T_,- _Key_,- _Value_) 


 _Key_  is the maximal key in  _T_, and is associated with  _Val_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_map(+ _T_,+ _G_,- _TN_) 


For all nodes  _Key_ in the tree  _T_, if the value associated with
key  _Key_ is  _Val0_ in tree  _T_, and if
`call(G,Val0,ValF)` holds, then the value associated with  _Key_
in  _TN_ is  _ValF_. Fails if or if `call(G,Val0,ValF)` is not
satisfiable for all  _Var0_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_lookupall(+ _Key_,- _Value_,+ _T_) 


Lookup all elements with key  _Key_ in the red-black tree
 _T_, returning the value  _Value_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_lookup(+ _Key_,- _Value_,+ _T_) 


Backtrack through all elements with key  _Key_ in the red-black tree
 _T_, returning for each the value  _Value_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_keys(+ _T_,+ _Keys_) 


 _Keys_ is an infix visit with all keys in tree  _T_. Keys will be
sorted, but may be duplicate.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_key_fold(+ _T_,+ _G_,+ _Acc0_, - _AccF_) 


For all nodes  _Key_ in the tree  _T_, if the value
associated with key  _Key_ is  _V_ in tree  _T_, if
`call(G,Key,V,Acc1,Acc2)` holds, then if  _VL_ is value of the
previous node in inorder, `call(G,KeyL,VL,_,Acc0)` must hold, and if
 _VR_ is the value of the next node in inorder,
`call(G,KeyR,VR,Acc1,_)` must hold.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_insert(+ _T0_,+ _Key_,? _Value_,+ _TF_) 


Add an element with key  _Key_ and  _Value_ to the tree
 _T0_ creating a new red-black tree  _TF_. Duplicated elements are not
allowed.

Add a new element with key  _Key_ and  _Value_ to the tree
 _T0_ creating a new red-black tree  _TF_. Fails is an element
with  _Key_ exists in the tree.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_fold(+ _T_,+ _G_,+ _Acc0_, - _AccF_) 


For all nodes  _Key_ in the tree  _T_, if the value
associated with key  _Key_ is  _V_ in tree  _T_, if
`call(G,V,Acc1,Acc2)` holds, then if  _VL_ is value of the
previous node in inorder, `call(G,VL,_,Acc0)` must hold, and if
 _VR_ is the value of the next node in inorder,
`call(G,VR,Acc1,_)` must hold.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_empty(? _T_) 


Succeeds if tree  _T_ is empty.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_delete(+ _T_,+ _Key_,- _Val_,- _TN_)

Delete element with key  _Key_ from the tree  _T_, returning the
value  _Val_ associated with the key and a new tree  _TN_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_delete(+ _T_,+ _Key_,- _TN_) 


Delete element with key  _Key_ from the tree  _T_, returning a new
tree  _TN_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_del_min(+ _T_,- _Key_,- _Val_,- _TN_) 


Delete the least element from the tree  _T_, returning the key
 _Key_, the value  _Val_ associated with the key and a new tree
 _TN_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_del_max(+ _T_,- _Key_,- _Val_,- _TN_) 


Delete the largest element from the tree  _T_, returning the key
 _Key_, the value  _Val_ associated with the key and a new tree
 _TN_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_clone(+ _T_,+ _NT_,+ _Nodes_) 


=Clone= the red-back tree into a new tree with the same keys as the
original but with all values set to unbound values. _Nodes_ is a list
containing all new nodes as pairs  _K-V_.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred rb_apply(+ _T_,+ _Key_,+ _G_,- _TN_) 


If the value associated with key  _Key_ is  _Val0_ in  _T_, and
if `call(G,Val0,ValF)` holds, then  _TN_ differs from
 _T_ only in that  _Key_ is associated with value  _ValF_ in
tree  _TN_. Fails if it cannot find  _Key_ in  _T_, or if
`call(G,Val0,ValF)` is not satisfiable.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred ord_list_to_rbtree(+ _L_, - _T_) 


 _T_ is the red-black tree corresponding to the mapping in ordered
list  _L_.



 */
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred is_rbtree(+ _T_) 


Check whether  _T_ is a valid red-black tree.

 
*/
EOF
sed -e "13r tmp" /Users/vsc/git/yap-6.3/library/rbtrees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/rbtrees.yap

#false
cat << "EOF" > tmp
/** @pred regexp(+ _RegExp_,+ _String_,+ _Opts_,? _SubMatchVars_)


Match regular expression  _RegExp_ to input string  _String_
according to options  _Opts_. The variable  _SubMatchVars_ should
be originally unbound or a list of unbound variables all will contain a
sequence of matches, that is, the head of  _SubMatchVars_ will
contain the characters in  _String_ that matched the leftmost
parenthesized subexpression within  _RegExp_, the next head of list
will contain the characters that matched the next parenthesized
subexpression to the right in  _RegExp_, and so on.

The options may be:

+ `nocase`: Causes upper-case characters  in   _String_ to
be treated  as  lower case during the matching process.
+ `indices`: Changes what  is  stored  in
 _SubMatchVars_. Instead  of storing the matching characters from
 _String_, each variable will contain a term of the form  _IO-IF_
giving the indices in  _String_ of the first and last characters  in
the  matching range of characters.



In general there may be more than one way to match a regular expression
to an input string.  For example,  consider the command

~~~~~
  regexp("(a*)b*","aabaaabb", [], [X,Y])
~~~~~
Considering only the rules given so far,  _X_ and  _Y_ could end up
with the values `"aabb"` and `"aa"`, `"aaab"` and
`"aaa"`, `"ab"` and `"a"`, or any of several other
combinations.  To resolve this potential ambiguity `regexp` chooses among
alternatives using the rule `first then longest`.  In other words, it
considers the possible matches in order working from left to right
across the input string and the pattern, and it attempts to match longer
pieces of the input string before shorter ones.  More specifically, the
following rules apply in decreasing order of priority:

+ If a regular expression could match  two  different parts of an
input string then it will match the one that begins earliest.

+ If a regular expression contains "|"  operators  then the leftmost matching sub-expression is chosen.

+ In \*, +, and ? constructs, longer matches are chosen in preference to shorter ones.

+ In sequences of expression  components  the  components are considered from left to right.

In the example above, `"(a\*)b\*"` matches `"aab"`: the
`"(a\*)"` portion of the pattern is matched first and it consumes
the leading `"aa"`; then the `"b\*"` portion of the pattern
consumes the next `"b"`.  Or, consider the following example: 

~~~~~
  regexp("(ab|a)(b*)c",  "abc", [], [X,Y,Z])
~~~~~

After this command  _X_ will be `"abc"`,  _Y_ will be
`"ab"`, and  _Z_ will be an empty string.  Rule 4 specifies that
`"(ab|a)"` gets first shot at the input string and Rule 2 specifies
that the `"ab"` sub-expression is checked before the `"a"`
sub-expression.  Thus the `"b"` has already been claimed before the
`"(b\*)"` component is checked and `(b\*)` must match an empty string.




 */
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/regexp.yap > x
     mv x /Users/vsc/git/yap-6.3/library/regexp.yap

#false
cat << "EOF" > tmp
/** @pred  socket_select(+ _SOCKETS_, - _NEWSTREAMS_, + _TIMEOUT_, + _STREAMS_, - _READSTREAMS_) [unsupported in YAP-6.3]

Interface to system call `select`, used for servers to wait for
connection requests or for data at sockets. The variable
 _SOCKETS_ is a list of form  _KEY-SOCKET_, where  _KEY_ is
an user-defined identifier and  _SOCKET_ is a socket descriptor. The
variable  _TIMEOUT_ is either `off`, indicating execution will
wait until something is available, or of the form  _SEC-USEC_, where
 _SEC_ and  _USEC_ give the seconds and microseconds before
socket_select/5 returns. The variable  _SOCKETS_ is a list of
form  _KEY-STREAM_, where  _KEY_ is an user-defined identifier
and  _STREAM_ is a stream descriptor

Execution of socket_select/5 unifies  _READSTREAMS_ from
 _STREAMS_ with readable data, and  _NEWSTREAMS_ with a list of
the form  _KEY-STREAM_, where  _KEY_ was the key for a socket
with pending data, and  _STREAM_ the stream descriptor resulting
from accepting the connection.  

 
*/
EOF
sed -e "225r tmp" /Users/vsc/git/yap-6.3/library/sockets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/sockets.yap

#false
cat << "EOF" > tmp
/** @pred  socket_buffering(+ _SOCKET_, - _MODE_, - _OLD_, + _NEW_) 


Set buffering for  _SOCKET_ in `read` or `write`
 _MODE_.  _OLD_ is unified with the previous status, and  _NEW_
receives the new status which may be one of `unbuf` or
`fullbuf`.

 
*/
EOF
sed -e "178r tmp" /Users/vsc/git/yap-6.3/library/sockets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/sockets.yap

#false
cat << "EOF" > tmp
/** @pred  socket_listen(+ _SOCKET_, + _LENGTH_) 


Interface to system call `listen`, used for servers to indicate
willingness to wait for connections at socket  _SOCKET_. The
integer  _LENGTH_ gives the queue limit for incoming connections,
and should be limited to `5` for portable applications. The socket
must be of type `SOCK_STREAM` or `SOCK_SEQPACKET`.

 
*/
EOF
sed -e "99r tmp" /Users/vsc/git/yap-6.3/library/sockets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/sockets.yap

#false
cat << "EOF" > tmp
/** @pred  socket_close(+ _SOCKET_) 



Close socket  _SOCKET_. Note that sockets used in
`socket_connect` (that is, client sockets) should not be closed with
`socket_close`, as they will be automatically closed when the
corresponding stream is closed with close/1 or `close/2`.

 
*/
EOF
sed -e "99r tmp" /Users/vsc/git/yap-6.3/library/sockets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/sockets.yap

#false
cat << "EOF" > tmp
/** @pred  socket_bind(+ _SOCKET_, ? _PORT_) 



Interface to system call `bind`, as used for servers: bind socket
to a port. Port information depends on the domain:

+ 'AF_UNIX'(+ _FILENAME_) (unsupported)
+ 'AF_FILE'(+ _FILENAME_)
use file name  _FILENAME_ for UNIX or local sockets.

+ 'AF_INET'(? _HOST_,?PORT)
If  _HOST_ is bound to an atom, bind to host  _HOST_, otherwise
if unbound bind to local host ( _HOST_ remains unbound). If port
 _PORT_ is bound to an integer, try to bind to the corresponding
port. If variable  _PORT_ is unbound allow operating systems to
choose a port number, which is unified with  _PORT_.



 
*/
EOF
sed -e "99r tmp" /Users/vsc/git/yap-6.3/library/sockets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/sockets.yap

#false
cat << "EOF" > tmp
/** @pred  socket_accept(+ _SOCKET_, - _STREAM_)

Accept a connection but do not return client information.

 
*/
EOF
sed -e "99r tmp" /Users/vsc/git/yap-6.3/library/sockets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/sockets.yap

#false
cat << "EOF" > tmp
/** @pred  socket_accept(+ _SOCKET_, - _CLIENT_, - _STREAM_) 


Interface to system call `accept`, used for servers to wait for
connections at socket  _SOCKET_. The stream descriptor  _STREAM_
represents the resulting connection.  If the socket belongs to the
domain `AF_INET`,  _CLIENT_ unifies with an atom containing
the IP address for the client in numbers and dots notation.

 
*/
EOF
sed -e "99r tmp" /Users/vsc/git/yap-6.3/library/sockets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/sockets.yap

#false
cat << "EOF" > tmp
/** @pred  hostname_address(? _HOSTNAME_,? _IP_ADDRESS_) 

 _HOSTNAME_ is an host name and  _IP_ADDRESS_ its IP
address in number and dots notation.




*/
EOF
sed -e "99r tmp" /Users/vsc/git/yap-6.3/library/sockets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/sockets.yap

#false
cat << "EOF" > tmp
/** @pred  current_host(? _HOSTNAME_) 

Unify  _HOSTNAME_ with an atom representing the fully qualified
hostname for the current host. Also succeeds if  _HOSTNAME_ is bound
to the unqualified hostname.

 
*/
EOF
sed -e "99r tmp" /Users/vsc/git/yap-6.3/library/sockets.yap > x
     mv x /Users/vsc/git/yap-6.3/library/sockets.yap

#false
cat << "EOF" > tmp
/** @pred splay_split(+ _Key_,? _Val_,+ _Tree_,- _LeftTree_,- _RightTree_) 


Construct and return two trees  _LeftTree_ and  _RightTree_,
where  _LeftTree_ contains all items in  _Tree_ less than
 _Key_, and  _RightTree_ contains all items in  _Tree_
greater than  _Key_. This operations destroys  _Tree_.




 */
EOF
sed -e "93r tmp" /Users/vsc/git/yap-6.3/library/splay.yap > x
     mv x /Users/vsc/git/yap-6.3/library/splay.yap

#false
cat << "EOF" > tmp
/** @pred splay_join(+ _LeftTree_,+ _RighTree_,- _NewTree_) 


Combine trees  _LeftTree_ and  _RighTree_ into a single
tree _NewTree_ containing all items from both trees. This operation
assumes that all items in  _LeftTree_ are less than all those in
 _RighTree_ and destroys both  _LeftTree_ and  _RighTree_.

 
*/
EOF
sed -e "93r tmp" /Users/vsc/git/yap-6.3/library/splay.yap > x
     mv x /Users/vsc/git/yap-6.3/library/splay.yap

#false
cat << "EOF" > tmp
/** @pred splay_insert(+ _Key_,? _Val_,+ _Tree_,- _NewTree_) 


Insert item  _Key_ in tree  _Tree_, assuming that it is not
there already. The variable  _Val_ unifies with a value for key
 _Key_, and the variable  _NewTree_ unifies with the new
tree. In our implementation,  _Key_ is not inserted if it is
already there: rather it is unified with the item already in the tree.

 
*/
EOF
sed -e "93r tmp" /Users/vsc/git/yap-6.3/library/splay.yap > x
     mv x /Users/vsc/git/yap-6.3/library/splay.yap

#false
cat << "EOF" > tmp
/** @pred splay_init(- _NewTree_) 


Initialize a new splay tree.

 
*/
EOF
sed -e "93r tmp" /Users/vsc/git/yap-6.3/library/splay.yap > x
     mv x /Users/vsc/git/yap-6.3/library/splay.yap

#false
cat << "EOF" > tmp
/** @pred splay_del(+ _Item_,+ _Tree_,- _NewTree_) 


Delete item  _Key_ from tree  _Tree_, assuming that it is present
already. The variable  _Val_ unifies with a value for key  _Key_,
and the variable  _NewTree_ unifies with the new tree. The predicate
will fail if  _Key_ is not present.

 
*/
EOF
sed -e "93r tmp" /Users/vsc/git/yap-6.3/library/splay.yap > x
     mv x /Users/vsc/git/yap-6.3/library/splay.yap

#true
cat << "EOF" > tmp
/** @pred working_directory(- _Old_,+ _New_) 



Unify  _Old_ with an absolute path to the current working directory
and change working directory to  _New_.  Use the pattern
`working_directory(CWD, CWD)` to get the current directory.  See
also `absolute_file_name/2` and chdir/1.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred tmpnam(- _File_) 



Interface with  _tmpnam_: obtain a new, unique file name  _File_.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred tmp_file(+_Base_, - _File_) 

Create a name for a temporary file.  _Base_ is an user provided
identifier for the category of file. The  _TmpName_ is guaranteed to
be unique. If the system halts, it will automatically remove all created
temporary files.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred system(+ _Command_,- _Res_)

Interface to `system`: execute command  _Command_ and unify
 _Res_ with the result.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred system

Start a new default shell and leave YAP in background until the shell
completes. YAP uses `/bin/sh` in Unix systems and `COMSPEC` in
WIN32.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred sleep(+ _Time_) 


Block the current thread for  _Time_ seconds. When YAP is compiled 
without multi-threading support, this predicate blocks the YAP process. 
The number of seconds must be a positive number, and it may an integer 
or a float. The Unix implementation uses `usleep` if the number of 
seconds is below one, and `sleep` if it is over a second. The WIN32 
implementation uses `Sleep` for both cases.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred shell(+ _Command_,- _Status_)

Execute command  _Command_ under a new shell and unify  _Status_
with the exit for the command. YAP will be in background until the
command completes. In Unix environments YAP uses the shell given by the
environment variable `SHELL` with the option `" -c "`. In
WIN32 environment YAP will use `COMSPEC` if `SHELL` is
undefined, in this case with the option `" /c "`.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred shell(+ _Command_)

Execute command  _Command_ under a new shell. YAP will be in
background until the command completes. In Unix environments YAP uses
the shell given by the environment variable `SHELL` with the option
`" -c "`. In WIN32 environment YAP will use `COMSPEC` if
`SHELL` is undefined, in this case with the option `" /c "`.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred shell 


Start a new shell and leave YAP in background until the shell
completes. YAP uses the shell given by the environment variable
`SHELL`. In WIN32 environment YAP will use `COMSPEC` if
`SHELL` is undefined.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred rename_file(+ _OldFile_,+ _NewFile_) 


Create file  _OldFile_ to  _NewFile_. This predicate uses the
`C` built-in function `rename`.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred popen(+ _Command_, + _TYPE_, - _Stream_) 


Interface to the <tt>popen</tt> function. It opens a process by creating a
pipe, forking and invoking  _Command_ on the current shell. Since a
pipe is by definition unidirectional the  _Type_ argument may be
`read` or `write`, not both. The stream should be closed
using close/1, there is no need for a special `pclose`
command.

The following example demonstrates the use of popen/3 to process
the output of a command, as exec/3 would do:

~~~~~{.prolog}
   ?- popen(ls,read,X),repeat, get0(X,C), (C = -1, ! ; put(C)).

X = 'C:\\cygwin\\home\\administrator' ?
~~~~~

The WIN32 implementation of popen/3 relies on exec/3.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred pid(- _Id_) 



Unify  _Id_ with the process identifier for the current
process. An interface to the <tt>getpid</tt> function.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred mktime(+_Datime_, - _Seconds_)

The `mktime/2` procedure receives a term of the form _datime(+ _Year_,
+ _Month_, + _DayOfTheMonth_, + _Hour_, + _Minute_, + _Second_)_ and
returns the number of _Seconds_ elapsed since 00:00:00 on January 1,
1970, Coordinated Universal Time (UTC).  The user provides information
on _Year_, _Month_, _DayOfTheMonth_, _Hour_, _Minute_, and
_Second_. The _Hour_ is given on local time. This function uses the
WIN32 `GetLocalTime` function or the Unix `mktime` function.

~~~~~
   ?- mktime(datime(2001,5,28,15,29,46),X).

X = 991081786 ? ;
~~~~~

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred mktemp( _Spec_,- _File_) 



Direct interface to `mktemp`: given a  _Spec_, that is a file
name with six  _X_ to it, create a file name  _File_. Use
tmpnam/1 instead.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred make_directory(+ _Dir_) 


Create a directory  _Dir_. The name of the directory must be an atom.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred host_name(- _Name_) 



Unify  _Name_ with a name for the current host. YAP uses the
`hostname` function in Unix systems when available, and the
`GetComputerName` function in WIN32 systems. 

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred host_id(- _Id_) 



Unify  _Id_ with an identifier of the current host. YAP uses the
`hostid` function when available, 

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred file_property(+ _File_,? _Property_) 


The atom  _File_ corresponds to an existing file, and  _Property_
will be unified with a property of this file. The properties are of the
form `type( _Type_)`, which gives whether the file is a regular
file, a directory, a fifo file, or of unknown type;
`size( _Size_)`, with gives the size for a file, and
`mod_time( _Time_)`, which gives the last time a file was
modified according to some Operating System dependent
timestamp; `mode( _mode_)`, gives the permission flags for the
file, and `linkto( _FileName_)`, gives the file pointed to by a
symbolic link. Properties can be obtained through backtracking:

~~~~~
   ?- file_property('Makefile',P).

P = type(regular) ? ;

P = size(2375) ? ;

P = mod_time(990826911) ? ;

no
~~~~~

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred file_exists(+ _File_,+ _Permissions_)

The atom  _File_ corresponds to an existing file with permissions
compatible with  _Permissions_. YAP currently only accepts for
permissions to be described as a number. The actual meaning of this
number is Operating System dependent.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred file_exists(+ _File_) 


The atom  _File_ corresponds to an existing file.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred exec(+ _Command_, _StandardStreams_,- _PID_) 


Execute command  _Command_ with its standard streams connected to
the list [_InputStream_,  _OutputStream_, _ErrorStream_]. The
process that executes the command is returned as  _PID_. The
command is executed by the default shell `bin/sh -c` in Unix.

The following example demonstrates the use of exec/3 to send a
command and process its output:

~~~~~
exec(ls,[std,pipe(S),null],P),repeat, get0(S,C), (C = -1, close(S) ! ; put(C)).
~~~~~

The streams may be one of standard stream, `std`, null stream,
`null`, or `pipe(S)`, where  _S_ is a pipe stream. Note
that it is up to the user to close the pipe.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred environ(? _EnvVar_,+ _EnvValue_) 


Unify environment variable  _EnvVar_ with its value  _EnvValue_,
if there is one. This predicate is backtrackable in Unix systems, but
not currently in Win32 configurations.

~~~~~
   ?- environ('HOME',X).

X = 'C:\\cygwin\\home\\administrator' ?
~~~~~

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred directory_files(+ _Dir_,+ _List_) 


Given a directory  _Dir_,  directory_files/2 procedures a
listing of all files and directories in the directory:

~~~~~
    ?- directory_files('.',L), writeq(L).
['Makefile.~1~','sys.so','Makefile','sys.o',x,..,'.']
~~~~~
The predicates uses the `dirent` family of routines in Unix
environments, and `findfirst` in WIN32.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred delete_file(+ _File_,+ _Opts_)

The `delete_file/2` procedure removes file  _File_ according to
options  _Opts_. These options are `directory` if one should
remove directories, `recursive` if one should remove directories
recursively, and `ignore` if errors are not to be reported.

This example is equivalent to using the delete_file/1 predicate:

~~~~~
   ?- delete_file(x, [recursive]).
~~~~~

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred delete_file(+ _File_) 


The delete_file/1 procedure removes file  _File_. If
 _File_ is a directory, remove the directory <em>and all its subdirectories</em>.

~~~~~
   ?- delete_file(x).
~~~~~

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred  working_directory(- _CurDir_,? _NextDir_) 


Fetch the current directory at  _CurDir_. If  _NextDir_ is bound
to an atom, make its value the current working directory.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred  system(+ _S_) 


Passes command  _S_ to the Bourne shell (on UNIX environments) or the
current command interpreter in WIN32 environments.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#false
cat << "EOF" > tmp
/** @pred  environ(+ _E_,- _S_) 





Given an environment variable  _E_ this predicate unifies the second argument  _S_ with its value.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/library/system.yap > x
     mv x /Users/vsc/git/yap-6.3/library/system.yap

#true
cat << "EOF" > tmp
/** @pred variant(? _Term1_, ? _Term2_) 



Succeed if  _Term1_ and  _Term2_ are variant terms.

 
*/
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#true
cat << "EOF" > tmp
/** @pred variables_within_term(+ _Variables_,? _Term_, - _OutputVariables_) 



Unify  _OutputVariables_ with the subset of the variables  _Variables_ that occurs in  _Term_.

 
*/
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#true
cat << "EOF" > tmp
/** @pred variable_in_term(? _Term_,? _Var_) 


Succeed if the second argument  _Var_ is a variable and occurs in
term  _Term_.

 
*/
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#true
cat << "EOF" > tmp
/** @pred unifiable(? _Term1_, ? _Term2_, - _Bindings_) 



Succeed if  _Term1_ and  _Term2_ are unifiable with substitution
 _Bindings_.




 */
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#true
cat << "EOF" > tmp
/** @pred term_hash(+ _Term_, ? _Hash_) 



If  _Term_ is ground unify  _Hash_ with a positive integer
calculated from the structure of the term. Otherwise the argument
 _Hash_ is left unbound. The range of the positive integer is from
`0` to, but not including, `33554432`.

 
*/
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#true
cat << "EOF" > tmp
/** @pred term_hash(+ _Term_, + _Depth_, + _Range_, ? _Hash_)


Unify  _Hash_ with a positive integer calculated from the structure
of the term.  The range of the positive integer is from `0` to, but
not including,  _Range_. If  _Depth_ is `-1` the whole term
is considered. Otherwise, the term is considered only up to depth
`1`, where the constants and the principal functor have depth
`1`, and an argument of a term with depth  _I_ has depth  _I+1_. 

 
*/
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#true
cat << "EOF" > tmp
/** @pred subsumes_chk(? _Term1_, ? _Term2_) 



Succeed if  _Term1_ subsumes  _Term2_ but does not bind any
variable in  _Term1_.

 
*/
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#true
cat << "EOF" > tmp
/** @pred subsumes(? _Term1_, ? _Term2_) 



Succeed if  _Term1_ subsumes  _Term2_.  Variables in term
 _Term1_ are bound so that the two terms become equal.

 
*/
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#true
cat << "EOF" > tmp
/** @pred new_variables_in_term(+ _Variables_,? _Term_, - _OutputVariables_) 



Unify  _OutputVariables_ with all variables occurring in  _Term_ that are not in the list  _Variables_.

 
*/
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#true
cat << "EOF" > tmp
/** @pred  term_subsumer(? _T1_, ? _T2_, ? _Subsumer_) 



Succeed if  _Subsumer_ unifies with the least general
generalization over  _T1_ and
 _T2_.

 
*/
EOF
sed -e "130r tmp" /Users/vsc/git/yap-6.3/library/terms.yap > x
     mv x /Users/vsc/git/yap-6.3/library/terms.yap

#false
cat << "EOF" > tmp
/** @pred tree_to_list(+ _Tree_, - _List_) 


Is the converse operation to list_to_tree.




 */
EOF
sed -e "84r tmp" /Users/vsc/git/yap-6.3/library/trees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/trees.yap

#false
cat << "EOF" > tmp
/** @pred tree_size(+ _Tree_, - _Size_) 


Calculates the number of elements in the  _Tree_.

 
*/
EOF
sed -e "84r tmp" /Users/vsc/git/yap-6.3/library/trees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/trees.yap

#false
cat << "EOF" > tmp
/** @pred put_label(+ _Index_, + _OldTree_, + _Label_, - _NewTree_) 


constructs a new tree the same shape as the old which moreover has the
same elements except that the  _Index_-th one is  _Label_.

 
*/
EOF
sed -e "84r tmp" /Users/vsc/git/yap-6.3/library/trees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/trees.yap

#false
cat << "EOF" > tmp
/** @pred map_tree(+ _Pred_, + _OldTree_, - _NewTree_) 


Holds when  _OldTree_ and  _NewTree_ are binary trees of the same shape
and `Pred(Old,New)` is true for corresponding elements of the two trees.

 
*/
EOF
sed -e "84r tmp" /Users/vsc/git/yap-6.3/library/trees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/trees.yap

#false
cat << "EOF" > tmp
/** @pred list_to_tree(+ _List_, - _Tree_) 


Takes a given  _List_ of  _N_ elements and constructs a binary
 _Tree_.

 
*/
EOF
sed -e "84r tmp" /Users/vsc/git/yap-6.3/library/trees.yap > x
     mv x /Users/vsc/git/yap-6.3/library/trees.yap

#false
cat << "EOF" > tmp
/** @pred trie_usage(+ _Trie_,- _Entries_,- _Nodes_,- _VirtualNodes_) 


Give statistics on trie  _Trie_, the number of entries,
 _Entries_, and the total number of nodes,  _Nodes_, and the
number of  _VirtualNodes_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_stats(- _Memory_,- _Tries_,- _Entries_,- _Nodes_) 


Give generic statistics on tries, including the amount of memory,
 _Memory_, the number of tries,  _Tries_, the number of entries,
 _Entries_, and the total number of nodes,  _Nodes_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_save(+ _Trie_,+ _FileName_) 


Dump trie  _Trie_ into file  _FileName_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_remove_subtree(+ _Ref_) 



Remove subtree rooted at handle  _Ref_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_remove_entry(+ _Ref_) 



Remove entry for handle  _Ref_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_put_entry(+ _Trie_,+ _Term_,- _Ref_) 



Add term  _Term_ to trie  _Trie_. The handle  _Ref_ gives
a reference to the term.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_print(+ _Trie_) 


Print trie  _Trie_ on standard output.




 */
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_open(- _Id_) 



Open a new trie with identifier  _Id_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_mode(? _Mode_) 



Unify  _Mode_ with trie operation mode. Allowed values are either
`std` (default) or `rev`.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_max_stats(- _Memory_,- _Tries_,- _Entries_,- _Nodes_) 


Give maximal statistics on tries, including the amount of memory,
 _Memory_, the number of tries,  _Tries_, the number of entries,
 _Entries_, and the total number of nodes,  _Nodes_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_load(+ _Trie_,+ _FileName_) 


Load trie  _Trie_ from the contents of file  _FileName_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_get_entry(+ _Ref_,- _Term_) 


Unify  _Term_ with the entry for handle  _Ref_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_close_all 



Close all available tries.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_close(+ _Id_) 



Close trie with identifier  _Id_.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred trie_check_entry(+ _Trie_,+ _Term_,- _Ref_) 



Succeeds if a variant of term  _Term_ is in trie  _Trie_. An handle
 _Ref_ gives a reference to the term.

 
*/
EOF
sed -e "149r tmp" /Users/vsc/git/yap-6.3/library/tries.yap > x
     mv x /Users/vsc/git/yap-6.3/library/tries.yap

#false
cat << "EOF" > tmp
/** @pred vertices(+ _Graph_, - _Vertices_) 


Unify  _Vertices_ with all vertices appearing in graph
 _Graph_. In the next example:

~~~~~{.prolog}
?- vertices([1-[3,5],2-[4],3-[],4-[5],5-[]], V).

L = [1,2,3,4,5]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred transitive_closure(+ _Graph_, + _Closure_) 


Generate the graph  _Closure_ as the transitive closure of graph
 _Graph_.
In the next example:

~~~~~{.prolog}
?- transitive_closure([1-[2,3],2-[4,5],4-[6]],L).

L = [1-[2,3,4,5,6],2-[4,5,6],4-[6]]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred top_sort(+ _Graph_, - _Sort_) 


Generate the set of nodes  _Sort_ as a topological sorting of graph
 _Graph_, if one is possible.
In the next example we show how topological sorting works for a linear graph:

~~~~~{.prolog}
?- top_sort([_138-[_219],_219-[_139], _139-[]],L).

L = [_138,_219,_139]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred top_sort(+ _Graph_, - _Sort0_, - _Sort_)

Generate the difference list  _Sort_- _Sort0_ as a topological
sorting of graph  _Graph_, if one is possible.

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred reachable(+ _Node_, + _Graph_, - _Vertices_) 


Unify  _Vertices_ with the set of all vertices in graph
 _Graph_ that are reachable from  _Node_. In the next example:

~~~~~{.prolog}
?- reachable(1,[1-[3,5],2-[4],3-[],4-[5],5-[]],V).

V = [1,3,5]
~~~~~




 */
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred neighbours(+ _Vertex_, + _Graph_, - _Vertices_) 


Unify  _Vertices_ with the list of neighbours of vertex  _Vertex_
in  _Graph_. In the next example:

~~~~~{.prolog}
?- neighbours(4,[1-[3,5],2-[4],3-[],
                 4-[1,2,7,5],5-[],6-[],7-[],8-[]], NL).

NL = [1,2,7,5]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred neighbors(+ _Vertex_, + _Graph_, - _Vertices_) 


Unify  _Vertices_ with the list of neighbors of vertex  _Vertex_
in  _Graph_. If the vertice is not in the graph fail. In the next
example:

~~~~~{.prolog}
?- neighbors(4,[1-[3,5],2-[4],3-[],
                4-[1,2,7,5],5-[],6-[],7-[],8-[]],
             NL).

NL = [1,2,7,5]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred edges(+ _Graph_, - _Edges_) 


Unify  _Edges_ with all edges appearing in graph
 _Graph_. In the next example:

~~~~~{.prolog}
?- vertices([1-[3,5],2-[4],3-[],4-[5],5-[]], V).

L = [1,2,3,4,5]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#true
cat << "EOF" > tmp
/** @pred del_vertices(+ _Graph_, + _Vertices_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by deleting the list of
vertices  _Vertices_ and all the edges that start from or go to a
vertex in  _Vertices_ to the graph  _Graph_. In the next example:

~~~~~{.prolog}
?- del_vertices([2,1],[1-[3,5],2-[4],3-[],
                 4-[5],5-[],6-[],7-[2,6],8-[]],NL).

NL = [3-[],4-[5],5-[],6-[],7-[6],8-[]]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#true
cat << "EOF" > tmp
/** @pred del_edges(+ _Graph_, + _Edges_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by removing the list of
edges  _Edges_ from the graph  _Graph_. Notice that no vertices
are deleted. In the next example:

~~~~~{.prolog}
?- del_edges([1-[3,5],2-[4],3-[],4-[5],5-[],
              6-[],7-[],8-[]],
             [1-6,2-3,3-2,5-7,3-2,4-5,1-3],NL).

NL = [1-[5],2-[4],3-[],4-[],5-[],6-[],7-[],8-[]]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#true
cat << "EOF" > tmp
/** @pred compose(+ _LeftGraph_, + _RightGraph_, - _NewGraph_) 


Compose the graphs  _LeftGraph_ and  _RightGraph_ to form  _NewGraph_.
In the next example:

~~~~~{.prolog}
?- compose([1-[2],2-[3]],[2-[4],3-[1,2,4]],L).

L = [1-[4],2-[1,2,4],3-[]]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred complement(+ _Graph_, - _NewGraph_) 


Unify  _NewGraph_ with the graph complementary to  _Graph_.
In the next example:

~~~~~{.prolog}
?- complement([1-[3,5],2-[4],3-[],
               4-[1,2,7,5],5-[],6-[],7-[],8-[]], NL).

NL = [1-[2,4,6,7,8],2-[1,3,5,6,7,8],3-[1,2,4,5,6,7,8],
      4-[3,5,6,8],5-[1,2,3,4,6,7,8],6-[1,2,3,4,5,7,8],
      7-[1,2,3,4,5,6,8],8-[1,2,3,4,5,6,7]]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#true
cat << "EOF" > tmp
/** @pred add_vertices(+ _Graph_, + _Vertices_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by adding the list of
vertices  _Vertices_ to the graph  _Graph_. In the next example:

~~~~~{.prolog}
?- add_vertices([1-[3,5],2-[4],3-[],4-[5],
                 5-[],6-[],7-[],8-[]],
                [0,2,9,10,11],
                   NG).

NG = [0-[],1-[3,5],2-[4],3-[],4-[5],5-[],
      6-[],7-[],8-[],9-[],10-[],11-[]]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#true
cat << "EOF" > tmp
/** @pred add_edges(+ _Graph_, + _Edges_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by adding the list of
edges  _Edges_ to the graph  _Graph_. In the next example:

~~~~~{.prolog}
?- add_edges([1-[3,5],2-[4],3-[],4-[5],5-[],6-[],
              7-[],8-[]],[1-6,2-3,3-2,5-7,3-2,4-5],NL).

NL = [1-[3,5,6],2-[3,4],3-[2],4-[5],5-[7],6-[],7-[],8-[]]
~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred  vertices_edges_to_ugraph(+ _Vertices_, + _Edges_, - _Graph_) 


Given a graph with a set of vertices  _Vertices_ and a set of edges
 _Edges_,  _Graph_ must unify with the corresponding
s-representation. Note that the vertices without edges will appear in
 _Vertices_ but not in  _Edges_. Moreover, it is sufficient for a
vertex to appear in  _Edges_.

~~~~~{.prolog}
?- vertices_edges_to_ugraph([],[1-3,2-4,4-5,1-5],L).

L = [1-[3,5],2-[4],3-[],4-[5],5-[]] ? 

~~~~~
In this case all edges are defined implicitly. The next example shows
three unconnected edges:

~~~~~{.prolog}
?- vertices_edges_to_ugraph([6,7,8],[1-3,2-4,4-5,1-5],L).

L = [1-[3,5],2-[4],3-[],4-[5],5-[],6-[],7-[],8-[]] ? 

~~~~~

 
*/
EOF
sed -e "295r tmp" /Users/vsc/git/yap-6.3/library/ugraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/ugraphs.yap

#false
cat << "EOF" > tmp
/** @pred undgraph_neighbours(+ _Vertex_, + _Graph_, - _Vertices_) 


Unify  _Vertices_ with the list of neighbours of vertex  _Vertex_
in  _Graph_.

 
*/
EOF
sed -e "6r tmp" /Users/vsc/git/yap-6.3/library/undgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/undgraphs.yap

#false
cat << "EOF" > tmp
/** @pred undgraph_neighbors(+ _Vertex_, + _Graph_, - _Vertices_) 


Unify  _Vertices_ with the list of neighbors of vertex  _Vertex_
in  _Graph_. If the vertice is not in the graph fail.

 
*/
EOF
sed -e "6r tmp" /Users/vsc/git/yap-6.3/library/undgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/undgraphs.yap

#false
cat << "EOF" > tmp
/** @pred undgraph_edges(+ _Graph_, - _Edges_) 


Unify  _Edges_ with all edges appearing in graph
 _Graph_.

 
*/
EOF
sed -e "6r tmp" /Users/vsc/git/yap-6.3/library/undgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/undgraphs.yap

#false
cat << "EOF" > tmp
/** @pred undgraph_del_vertices(+ _Graph_, + _Vertices_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by deleting the list of
vertices  _Vertices_ and all the edges that start from or go to a
vertex in  _Vertices_ to the graph  _Graph_.

 
*/
EOF
sed -e "6r tmp" /Users/vsc/git/yap-6.3/library/undgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/undgraphs.yap

#false
cat << "EOF" > tmp
/** @pred undgraph_del_edges(+ _Graph_, + _Edges_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by removing the list of
edges  _Edges_ from the graph  _Graph_. Notice that no vertices
are deleted.

 
*/
EOF
sed -e "6r tmp" /Users/vsc/git/yap-6.3/library/undgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/undgraphs.yap

#false
cat << "EOF" > tmp
/** @pred undgraph_add_vertices(+ _Graph_, + _Vertices_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by adding the list of
vertices  _Vertices_ to the graph  _Graph_.

 
*/
EOF
sed -e "6r tmp" /Users/vsc/git/yap-6.3/library/undgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/undgraphs.yap

#false
cat << "EOF" > tmp
/** @pred undgraph_add_edges(+ _Graph_, + _Edges_, - _NewGraph_) 


Unify  _NewGraph_ with a new graph obtained by adding the list of
edges  _Edges_ to the graph  _Graph_.

 
*/
EOF
sed -e "6r tmp" /Users/vsc/git/yap-6.3/library/undgraphs.yap > x
     mv x /Users/vsc/git/yap-6.3/library/undgraphs.yap

#false
cat << "EOF" > tmp
/** @pred  char_type(? _Char_, ? _Type_) 


Tests or generates alternative  _Types_ or  _Chars_. The
character-types are inspired by the standard `C`
`<ctype.h>` primitives.

+  `alnum`
     _Char_ is a letter (upper- or lowercase) or digit.

+ `alpha`
    _Char_ is a letter (upper- or lowercase).

+ `csym`
    _Char_ is a letter (upper- or lowercase), digit or the underscore (_). These are valid C- and Prolog symbol characters.

+ `csymf`
    _Char_ is a letter (upper- or lowercase) or the underscore (_). These are valid first characters for C- and Prolog symbols

+ `ascii`
    _Char_ is a 7-bits ASCII character (0..127).

+ `white`
    _Char_ is a space or tab. E.i. white space inside a line.

+ `cntrl`
    _Char_ is an ASCII control-character (0..31).
 
+ `digit`
    _Char_ is a digit.

+ `digit( _Weight_)`
    _Char_ is a digit with value _Weight_. I.e. `char_type(X, digit(6))` yields X =  aaasaá'6'. Useful for parsing numbers.

+ `xdigit( _Weight_)`
    _Char_ is a hexa-decimal digit with value  _Weight_. I.e. char_type(a, xdigit(X) yields X = '10'. Useful for parsing numbers.

+ `graph`
    _Char_ produces a visible mark on a page when printed. Note that the space is not included!

+ `lower`
    _Char_ is a lower-case letter.

+ `lower(Upper)`
    _Char_ is a lower-case version of  _Upper_. Only true if _Char_ is lowercase and  _Upper_ uppercase.

+ `to_lower(Upper)`
 _Char_ is a lower-case version of Upper. For non-letters, or letter without case,  _Char_ and Lower are the same. See also upcase_atom/2 and downcase_atom/2.

+ `upper`
 _Char_ is an upper-case letter.

+ `upper(Lower)`
 _Char_ is an upper-case version of Lower. Only true if  _Char_ is uppercase and Lower lowercase.

+ `to_upper(Lower)`
 _Char_ is an upper-case version of Lower. For non-letters, or letter without case,  _Char_ and Lower are the same. See also upcase_atom/2 and downcase_atom/2.

+ `punct`
 _Char_ is a punctuation character. This is a graph character that is not a letter or digit.

+ `space`
 _Char_ is some form of layout character (tab, vertical-tab, newline, etc.).

+ `end_of_file`
 _Char_ is -1.

+ `end_of_line`
 _Char_ ends a line (ASCII: 10..13).

+ `newline`
 _Char_ is a the newline character (10).

+ `period`
 _Char_ counts as the end of a sentence (.,!,?).

+ `quote`
 _Char_ is a quote-character.

+ `paren(Close)`
 _Char_ is an open-parenthesis and Close is the corresponding close-parenthesis. 


+ `code_type(? _Code_, ? _Type_)`


As char_type/2, but uses character-codes rather than
one-character atoms. Please note that both predicates are as
flexible as possible. They handle either representation if the
argument is instantiated and only will instantiate with an integer
code or one-character atom depending of the version used. See also
the prolog-flag double_quotes and the built-in predicates 
atom_chars/2 and atom_codes/2.




 */
EOF
sed -e "459r tmp" /Users/vsc/git/yap-6.3/os/pl-ctype.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-ctype.c

#false
cat << "EOF" > tmp
/** @pred  write_canonical(+ _S_,+ _T_) is iso

Displays term  _T_ on the stream  _S_. Atoms are quoted when
necessary, and operators are ignored.

 
*/
EOF
sed -e "5891r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  print(+ _S_, _T_)

Prints term  _T_ to the stream  _S_ instead of to the current output
stream.

 
*/
EOF
sed -e "5890r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  writeq(+ _S_, _T_) is iso

As writeq/1, but the output is sent to the stream  _S_.

 
*/
EOF
sed -e "5889r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  write(+ _S_, _T_) is iso

Writes term  _T_ to stream  _S_ instead of to the current output
stream.

 
*/
EOF
sed -e "5888r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  nl(+ _S_) is iso

Outputs a new line to stream  _S_.




 */
EOF
sed -e "5885r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  writeln( _T_) is iso 


Same as write/1 followed by nl/0.

 
*/
EOF
sed -e "5884r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  print( _T_) 


Prints the term  _T_ to the current output stream using write/1
unless T is bound and a call to the user-defined  predicate
`portray/1` succeeds. To do pretty  printing of terms the user should
define suitable clauses for `portray/1` and use print/1.

 
*/
EOF
sed -e "5883r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  writeq( _T_) is iso 


Writes the term  _T_, quoting names to make the result acceptable to
the predicate `read` whenever necessary.

 
*/
EOF
sed -e "5882r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  write( _T_) is iso 


The term  _T_ is written to the current output stream according to
the operator declarations in force.

 
*/
EOF
sed -e "5881r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  write_term(+ _S_, + _T_, + _Opts_) is iso

Displays term  _T_ on the current output stream, according to the same
options used by `write_term/3`.

 
*/
EOF
sed -e "5880r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  write_term(+ _T_, + _Opts_) is iso 


Displays term  _T_ on the current output stream, according to the
following options:

+ quoted(+ _Bool_) is iso
If `true`, quote atoms if this would be necessary for the atom to
be recognized as an atom by YAP's parser. The default value is
`false`.

+ ignore_ops(+ _Bool_) is iso
If `true`, ignore operator declarations when writing the term. The
default value is `false`.

+ numbervars(+ _Bool_) is iso
If `true`, output terms of the form
`$VAR(N)`, where  _N_ is an integer, as a sequence of capital
letters. The default value is `false`.

+ portrayed(+ _Bool_)
If `true`, use <tt>portray/1</tt> to portray bound terms. The default
value is `false`.

+ portray(+ _Bool_)
If `true`, use <tt>portray/1</tt> to portray bound terms. The default
value is `false`.

+ max_depth(+ _Depth_)
If `Depth` is a positive integer, use <tt>Depth</tt> as
the maximum depth to portray a term. The default is `0`, that is,
unlimited depth.

+ priority(+ _Piority_)
If `Priority` is a positive integer smaller than `1200`, 
give the context priority. The default is `1200`.

+ cycles(+ _Bool_)
Do not loop in rational trees (default).


 
*/
EOF
sed -e "5879r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  write_canonical(+ _T_) is iso 


Displays term  _T_ on the current output stream. Atoms are quoted
when necessary, and operators are ignored, that is, the term is written
in standard parenthesized prefix notation.

 
*/
EOF
sed -e "5878r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  nl is iso 


Outputs a new line to the current output stream.




 */
EOF
sed -e "5877r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get0(- _C_) 


The next character from the current input stream is consumed, and then
unified with  _C_. There are no restrictions on the possible
values of the ASCII code for the character, but the character will be
internally converted by YAP.

 
*/
EOF
sed -e "5755r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get0(+ _S_,- _C_)

The same as `get0(C)`, but from stream  _S_.

 
*/
EOF
sed -e "5754r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  put_char(+ _N_) is iso 


Outputs to the current output stream the character who is used to build
the representation of atom `A`. The current output stream must be a
text stream.

 
*/
EOF
sed -e "5731r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  put_char(+ _S_,+ _A_) is iso

As `put_char(A)`, but to text stream  _S_.

 
*/
EOF
sed -e "5730r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  peek_char(- _C_) is iso 


If  _C_ is unbound, or is an atom representation of a character, and
the current stream is a text stream, read the next character from the
current stream and unify its atom representation with  _C_, while
leaving the current stream position unaltered.

 
*/
EOF
sed -e "5445r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  peek_char(+ _S_,- _C_) is iso

If  _C_ is unbound, or is an atom representation of a character, and
the stream  _S_ is a text stream, read the next character from that
stream and unify its representation as an atom with  _C_, while leaving
the current stream position unaltered.

 
*/
EOF
sed -e "5429r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  peek_code(- _C_) is iso 


If  _C_ is unbound, or is the code for a character, and
the current stream is a text stream, read the next character from the
current stream and unify its code with  _C_, while
leaving the current stream position unaltered.

 
*/
EOF
sed -e "5413r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  peek_code(+ _S_,- _C_) is iso

If  _C_ is unbound, or is an atom representation of a character, and
the stream  _S_ is a text stream, read the next character from that
stream and unify its representation as an atom with  _C_, while leaving
the current stream position unaltered.

 
*/
EOF
sed -e "5397r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  peek_byte(- _C_) is iso 


If  _C_ is unbound, or is a character code, and the current stream is a
binary stream, read the next byte from the current stream and unify its
code with  _C_, while leaving the current stream position unaltered.

 
*/
EOF
sed -e "5381r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  peek_byte(+ _S_,- _C_) is iso

If  _C_ is unbound, or is a character code, and  _S_ is a binary
stream, read the next byte from the current stream and unify its code
with  _C_, while leaving the current stream position unaltered.

 
*/
EOF
sed -e "5365r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  at_end_of_stream is iso 


Succeed if the current stream has stream position end-of-stream or
past-end-of-stream.

 
*/
EOF
sed -e "5309r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  at_end_of_stream(+ _S_) is iso

Succeed if the stream  _S_ has stream position end-of-stream or
past-end-of-stream. Note that  _S_ must be a readable stream.

 
*/
EOF
sed -e "5295r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  line_position(+ _Stream_,- _LinePosition_) 


Unify  _LinePosition_ with the position on current text stream
 _Stream_.

 
*/
EOF
sed -e "5236r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  line_count(+ _Stream_,- _LineNumber_) 


Unify  _LineNumber_ with the line number for the  _Stream_.

 
*/
EOF
sed -e "5212r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  character_count(+ _Stream_,- _CharacterCount_) 


Unify  _CharacterCount_ with the number of characters written to or
read to  _Stream_.

 
*/
EOF
sed -e "5189r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  current_output(- _S_) is iso 


Unify  _S_ with the current output stream.

 
*/
EOF
sed -e "5150r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  current_input(- _S_) is iso 


Unify  _S_ with the current input stream.

 
*/
EOF
sed -e "5136r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  set_output(+ _S_) is iso 


Set stream  _S_ as the current output stream. Predicates like
write/1 and put/1 will start using stream  _S_.

 
*/
EOF
sed -e "5114r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  set_input(+ _S_) is iso 


Set stream  _S_ as the current input stream. Predicates like read/1
and get/1 will start using stream  _S_.

 
*/
EOF
sed -e "5091r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  set_stream_position(+ _S_, + _POS_) is iso 


Given a stream position  _POS_ for a stream  _S_, set the current
stream position for  _S_ to be  _POS_.

 
*/
EOF
sed -e "4985r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  flush_output(+ _S_) is iso

Send all data in the output buffer for stream  _S_.

 
*/
EOF
sed -e "4915r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  flush_output is iso 


Send out all data in the output buffer of the current output stream.

 
*/
EOF
sed -e "4902r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  is_stream( _S_) 


Succeeds if  _S_ is a currently open stream.

 
*/
EOF
sed -e "4857r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  stream_property(? _Stream_,? _Prop_) is iso 



Obtain the properties for the open streams. If the first argument is
unbound, the procedure will backtrack through all open
streams. Otherwise, the first argument must be a stream term (you may
use `current_stream` to obtain a current stream given a file name).

The following properties are recognized:



+ file_name( _P_)
An atom giving the file name for the current stream. The file names are
user_input, user_output, and user_error for the
standard streams.

+ mode( _P_)
The mode used to open the file. It may be one of `append`,
`read`, or `write`.

+ input
The stream is readable.

+ output
The stream is writable.

+ alias( _A_)
ISO-Prolog primitive for stream aliases. <tt>YAP</tt> returns one of the
existing aliases for the stream.

+ position( _P_)
A term describing the position in the stream.

+ end_of_stream( _E_)
Whether the stream is `at` the end of stream, or it has found the
end of stream and is `past`, or whether it has `not` yet
reached the end of stream.

+ eof_action( _A_)
The action to take when trying to read after reaching the end of
stream. The action may be one of `error`, generate an error,
`eof_code`, return character code `-1`, or `reset` the
stream.

+ reposition( _B_)
Whether the stream can be repositioned or not, that is, whether it is
seekable.

+ type( _T_)
Whether the stream is a `text` stream or a `binary` stream.

+ bom(+ _Bool_)
If present and `true`, a BOM (<em>Byte Order Mark</em>) was
detected while opening the file for reading or a BOM was written while
opening the stream. See BOM for details.

+ encoding(+ _Encoding_)
Query the encoding used for text.  See Encoding for an
overview of wide character and encoding issues in YAP.

+ representation_errors(+ _Mode_)
Behaviour when writing characters to the stream that cannot be
represented by the encoding.  The behaviour is one of `error`
(throw and Input/Output error exception), `prolog` (write `\u...\`
escape code or `xml` (write `\&#...;` XML character entity).
The initial mode is `prolog` for the user streams and
`error` for all other streams. See also Encoding and
`open/4`.



+ current_line_number(- _LineNumber_) 


Unify  _LineNumber_ with the line number for the current stream.

 
*/
EOF
sed -e "4644r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  close(+ _S_,+ _O_) is iso

Closes the stream  _S_, following options  _O_. 

The only valid options are `force(true)` and `force(false)`.
YAP currently ignores these options.

 
*/
EOF
sed -e "4164r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  close(+ _S_) is iso 


Closes the stream  _S_. If  _S_ does not stand for a stream
currently opened an error is reported. The streams user_input,
user_output, and user_error can never be closed.

 
*/
EOF
sed -e "4141r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  told 


Closes the current output stream, and the user's terminal becomes again
the current output stream. It is important to remember to close streams
after having finished using them, as the maximum number of
simultaneously opened streams is 17.

 
*/
EOF
sed -e "3984r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  telling(- _S_) 


The current output stream is unified with  _S_.

 
*/
EOF
sed -e "3964r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  tell(+ _S_) 


If  _S_ is a currently opened stream for output, it becomes the
current output stream. If  _S_ is an atom it is taken to be a
filename.  If there is no output stream currently associated with it,
then it is opened for output, and the new output stream created becomes
the current output stream. If it is not possible to open the file, an
error occurs.  If there is a single opened output stream currently
associated with the file, then it becomes the current output stream; if
there are more than one in that condition, one of them is chosen.

Whenever  _S_ is a stream not currently opened for output, an error
may be reported, depending on the state of the file_errors flag. The
predicate just fails, if  _S_ is neither a stream nor an atom.

 
*/
EOF
sed -e "3947r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  seeing(- _S_) 


The current input stream is unified with  _S_.

 
*/
EOF
sed -e "3875r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  seen 


Closes the current input stream (see 6.7.).




 */
EOF
sed -e "3862r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  see(+ _S_) 


If  _S_ is a currently opened input stream then it is assumed to be
the current input stream. If  _S_ is an atom it is taken as a
filename. If there is no input stream currently associated with it, then
it is opened for input, and the new input stream thus created becomes
the current input stream. If it is not possible to open the file, an
error occurs.  If there is a single opened input stream currently
associated with the file, it becomes the current input stream; if there
are more than one in that condition, then one of them is chosen.

When  _S_ is a stream not currently opened for input, an error may be
reported, depending on the state of the `file_errors` flag. If
 _S_ is neither a stream nor an atom the predicates just fails.

 
*/
EOF
sed -e "3850r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  open(+ _F_,+ _M_,- _S_) is iso 


Opens the file with name  _F_ in mode  _M_ (`read`, `write` or
`append`), returning  _S_ unified with the stream name.

At most, there are 17 streams  opened at the same time. Each stream is
either an input or an output stream but not both. There are always 3
open streams:  user_input for reading, user_output for writing
and user_error for writing. If there is no  ambiguity, the atoms
user_input and user_output may be referred to as  `user`.

The `file_errors` flag controls whether errors are reported when in
mode `read` or `append` the file  _F_ does not exist or is not
readable, and whether in mode `write` or `append` the file is not
writable.

*/
EOF
sed -e "3732r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred open(+ _F_,+ _M_,- _S_,+ _Opts_) is iso

Opens the file with name  _F_ in mode  _M_ (`read`,  `write` or
`append`), returning  _S_ unified with the stream name, and following
these options:



+ `type(+ _T_)` is iso

  Specify whether the stream is a `text` stream (default), or a
`binary` stream.

+ `reposition(+ _Bool_)` is iso
  Specify whether it is possible to reposition the stream (`true`), or
not (`false`). By default, YAP enables repositioning for all
files, except terminal files and sockets.

+ `eof(+ _Action_)` is iso

  Specify the action to take if attempting to input characters from a
stream where we have previously found an `end_of_file`. The possible
actions are `error`, that raises an error, `reset`, that tries to
reset the stream and is used for `tty` type files, and `eof_code`,
which generates a new `end_of_file` (default for non-tty files).

+ `alias(+ _Name_)` is iso

  Specify an alias to the stream. The alias <tt>Name</tt> must be an atom. The
alias can be used instead of the stream descriptor for every operation
concerning the stream.

    The operation will fail and give an error if the alias name is already
in use. YAP allows several aliases for the same file, but only
one is returned by stream_property/2

+ `bom(+ _Bool_)`

  If present and `true`, a BOM (<em>Byte Order Mark</em>) was
detected while opening the file for reading or a BOM was written while
opening the stream. See BOM for details.

+ `encoding(+ _Encoding_)`

Set the encoding used for text.  See Encoding for an overview of
wide character and encoding issues.

+ `representation_errors(+ _Mode_)`

  Change the behaviour when writing characters to the stream that cannot
be represented by the encoding.  The behaviour is one of `error`
(throw and Input/Output error exception), `prolog` (write `\u...\`
escape code or `xml` (write `\&#...;` XML character entity).
The initial mode is `prolog` for the user streams and
`error` for all other streams. See also Encoding.

+ `expand_filename(+ _Mode_)`

  If  _Mode_ is `true` then do filename expansion, then ask Prolog
to do file name expansion before actually trying to opening the file:
this includes processing `~` characters and processing `$`
environment variables at the beginning of the file. Otherwise, just try
to open the file using the given name.

  The default behavior is given by the Prolog flag
open_expands_filename.



 
*/
EOF
sed -e "3703r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  tab(+ _N_) 


Outputs  _N_ spaces to the current output stream.

 
*/
EOF
sed -e "3300r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  tab(+ _S_,+ _N_)

The same as tab/1, but using stream  _S_.

 
*/
EOF
sed -e "3286r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred prompt(- _A_,+ _B_) 


Changes YAP input prompt from  _A_ to  _B_.

 
*/
EOF
sed -e "3189r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get_char(- _C_) is iso 


If  _C_ is unbound, or is an atom representation of a character, and
the current stream is a text stream, read the next character from the
current stream and unify its atom representation with  _C_.

 
*/
EOF
sed -e "3112r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get_char(+ _S_,- _C_) is iso

If  _C_ is unbound, or is an atom representation of a character, and
the stream  _S_ is a text stream, read the next character from that
stream and unify its representation as an atom with  _C_.

 
*/
EOF
sed -e "3096r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get_code(- _C_) is iso 


If  _C_ is unbound, or is the code for a character, and
the current stream is a text stream, read the next character from the
current stream and unify its code with  _C_.

 
*/
EOF
sed -e "3060r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get_code(+ _S_,- _C_) is iso

If  _C_ is unbound, or is a character code, and the stream  _S_ is a
text stream, read the next character from that stream and unify its
code with  _C_.

 
*/
EOF
sed -e "3044r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get_byte(- _C_) is iso 


If  _C_ is unbound, or is a character code, and the current stream is a
binary stream, read the next byte from the current stream and unify its
code with  _C_.

 
*/
EOF
sed -e "3002r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get_byte(+ _S_,- _C_) is iso

If  _C_ is unbound, or is a character code, and the stream  _S_ is a
binary stream, read the next byte from that stream and unify its
code with  _C_.

 
*/
EOF
sed -e "2985r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  skip(+ _S_,- _C_)

Like skip/1, but using stream  _S_ instead of the current
input stream.

 
*/
EOF
sed -e "2917r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  skip(+ _N_) 


Skips input characters until the next occurrence of the character with
ASCII code  _N_. The argument to this predicate can take the same forms
as those for `put` (see 6.11).

 
*/
EOF
sed -e "2902r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get(+ _S_,- _C_)

The same as `get(C)`, but from stream  _S_.

 
*/
EOF
sed -e "2867r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  get(- _C_) 


The next non-blank character from the current input stream is unified
with  _C_. Blank characters are the ones whose ASCII codes are not
greater than 32. If there are no more non-blank characters in the
stream,  _C_ is unified with -1. If `end_of_stream` has already
been reached in the previous reading, this call will give an error message.

 
*/
EOF
sed -e "2853r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  put(+ _N_) 


Outputs to the current output stream the character whose ASCII code is
 _N_. The character  _N_ must be a legal ASCII character code, an
expression yielding such a code, or a list in which case only the first
element is used.

 
*/
EOF
sed -e "2808r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  put(+ _S_,+ _N_)

As `put(N)`, but to stream  _S_.

 
*/
EOF
sed -e "2790r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  put_code(+ _N_) is iso 


Outputs to the current output stream the character whose ASCII code is
 _N_. The current output stream must be a text stream. The character
 _N_ must be a legal ASCII character code, an expression yielding such
a code, or a list in which case only the first element is used.

 
*/
EOF
sed -e "2776r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  put_code(+ _S_,+ _N_) is iso

As `put_code(N)`, but to text stream  _S_.

 
*/
EOF
sed -e "2749r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  put_byte(+ _N_) is iso 


Outputs to the current output stream the character whose code is
 _N_. The current output stream must be a binary stream.

 
*/
EOF
sed -e "2713r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  put_byte(+ _S_,+ _N_) is iso

As `put_byte(N)`, but to binary stream  _S_.

 
*/
EOF
sed -e "2699r tmp" /Users/vsc/git/yap-6.3/os/pl-file.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-file.c

#false
cat << "EOF" > tmp
/** @pred  file_name_extension(? _Base_,? _Extension_, ? _Name_) 



This predicate is used to add, remove or test filename extensions. The
main reason for its introduction is to deal with different filename
properties in a portable manner. If the file system is
case-insensitive, testing for an extension will be done
case-insensitive too.  _Extension_ may be specified with or
without a leading dot (.). If an  _Extension_ is generated, it
will not have a leading dot.

 
*/
EOF
sed -e "1231r tmp" /Users/vsc/git/yap-6.3/os/pl-files.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-files.c

#false
cat << "EOF" > tmp
/** @pred  file_base_name(+ _Name_,- _FileName_) 


Give the path a full path  _FullPath_ extract the  _FileName_.

 
*/
EOF
sed -e "967r tmp" /Users/vsc/git/yap-6.3/os/pl-files.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-files.c

#false
cat << "EOF" > tmp
/** @pred  access_file(+ _F_,+ _M_) 

Is the file accessible?

 
*/
EOF
sed -e "838r tmp" /Users/vsc/git/yap-6.3/os/pl-files.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-files.c

#false
cat << "EOF" > tmp
/** @pred atom_to_term(+ _Atom_, - _Term_, - _Bindings_) 


Use  _Atom_ as input to read_term/2 using the option `variable_names` and return the read term in  _Term_ and the variable bindings in  _Bindings_.  _Bindings_ is a list of `Name = Var` couples, thus providing access to the actual variable names. See also read_term/2. If Atom has no valid syntax, a syntax_error exception is raised.

 
*/
EOF
sed -e "1563r tmp" /Users/vsc/git/yap-6.3/os/pl-read.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-read.c

#false
cat << "EOF" > tmp
/** @pred read_term(- _T_,+ _Options_) is iso 


Reads term  _T_ from the current input stream with execution
controlled by the following options:

+ term_position(- _Position_) 

Unify  _Position_ with a term describing the position of the stream
at the start of parse. Use stream_position_data/3 to obtain extra
information.

+ singletons(- _Names_) 

Unify  _Names_ with a list of the form  _Name=Var_, where
 _Name_ is the name of a non-anonymous singleton variable in the
original term, and `Var` is the variable's representation in
YAP.
The variables occur in left-to-right traversal order.

+ syntax_errors(+ _Val_) 

Control action to be taken after syntax errors. See yap_flag/2
for detailed information.

+ variables(- _Names_) 

Unify  _Names_ with a list of the form  _Name=Var_, where  _Name_ is
the name of a non-anonymous variable in the original term, and  _Var_
is the variable's representation in YAP.
The variables occur in left-to-right traversal order.


*/
EOF
sed -e "1448r tmp" /Users/vsc/git/yap-6.3/os/pl-read.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-read.c

#false
cat << "EOF" > tmp
/** @pred  read_term(+ _S_,- _T_,+ _Options_) is iso

Reads term  _T_ from stream  _S_ with execution controlled by the
same options as read_term/2.

 
*/
EOF
sed -e "1380r tmp" /Users/vsc/git/yap-6.3/os/pl-read.c > x
     mv x /Users/vsc/git/yap-6.3/os/pl-read.c

#false
cat << "EOF" > tmp
/** @pred mtbdd_new(? _Exp_, - _BddHandle_) 

create a new algebraic decision diagram (ADD) from the logical
expression  _Exp_. The expression may include:

+ Logical Variables:
a leaf-node can be a logical variable, or <em>parameter</em>.
+ Number
a leaf-node can also be any number
+ _X_ \*  _Y_
product
+ _X_ +  _Y_
sum
+ _X_ -  _Y_
subtraction
+ or( _X_,  _Y_),  _X_ \/  _Y_
logical or


 
*/
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#false
cat << "EOF" > tmp
/** @pred bdd_tree(+ _BDDHandle_,  _Term_) 

Convert the BDD or ADD represented by  _BDDHandle_ to a Prolog term
of the form `bdd( _Dir_,  _Nodes_,  _Vars_)` or `mtbdd( _Nodes_,  _Vars_)`, respectively. The arguments are:

+ 
 _Dir_ direction of the BDD, usually 1
+ 
 _Nodes_ list of nodes in the BDD or ADD. 

In a BDD nodes may be <tt>pp</tt> (both terminals are positive) or <tt>pn</tt>
(right-hand-side is negative), and have four arguments: a logical
variable that will be bound to the value of the node, the logical
variable corresponding to the node, a logical variable, a 0 or a 1 with
the value of the left-hand side, and a logical variable, a 0 or a 1
with the right-hand side.

+ 
 _Vars_ are the free variables in the original BDD, or the parameters of the BDD/ADD.

As an example, the BDD for the expression `X+(Y+X)\*(-Z)` becomes:

~~~~~
bdd(1,[pn(N2,X,1,N1),pp(N1,Y,N0,1),pn(N0,Z,1,1)],vs(X,Y,Z))
~~~~~

 
*/
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#false
cat << "EOF" > tmp
/** @pred bdd_to_probability_sum_product(+ _BDDHandle_, - _Probs_, - _Prob_)
Each node in a BDD is given a probability  _Pi_. The total
probability of a corresponding sum-product network is  _Prob_, and
the probabilities of the inner nodes are  _Probs_.

In Prolog, this predicate would correspond to computing the value of a
BDD. The input variables will be bound to probabilities, eg
`[ _X_, _Y_, _Z_] = [0.3.0.7,0.1]`, and the previous
`eval_bdd` would operate over real numbers:

~~~~~
    Tree = bdd(1, T, _Vs),
    reverse(T, RT),
    foldl(eval_prob, RT, _, V).

eval_prob(pp(P,X,L,R), _, P) :-
    P is  X * L +  (1-X) * R.
eval_prob(pn(P,X,L,R), _, P) :-
    P is  X * L + (1-X) * (1-R).
~~~~~
 
*/
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#false
cat << "EOF" > tmp
/** @pred bdd_to_probability_sum_product(+ _BDDHandle_, - _Prob_) 

Each node in a BDD is given a probability  _Pi_. The total
probability of a corresponding sum-product network is  _Prob_.

 
*/
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#false
cat << "EOF" > tmp
/** @pred bdd_size(+ _BDDHandle_, - _Size_) 

Unify  _Size_ with the number of nodes in  _BDDHandle_.

 
*/
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#false
cat << "EOF" > tmp
/** @pred bdd_print(+ _BDDHandle_, + _File_) 

Output bdd  _BDDHandle_ as a dot file to  _File_.

 
*/
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#false
cat << "EOF" > tmp
/** @pred bdd_new(? _Exp_, - _BddHandle_) 

create a new BDD from the logical expression  _Exp_. The expression
may include:

+ Logical Variables:
a leaf-node can be a logical variable.
+ Constants 0 and 1
a leaf-node can also be one of these two constants.
+ or( _X_,  _Y_),  _X_ \/  _Y_,  _X_ +  _Y_
disjunction
+ and( _X_,  _Y_),  _X_ /\  _Y_,  _X_ \*  _Y_
conjunction
+ nand( _X_,  _Y_)
negated conjunction@
+ nor( _X_,  _Y_)
negated disjunction
+ xor( _X_,  _Y_)
exclusive or
+ not( _X_), - _X_
negation


 
*/
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#false
cat << "EOF" > tmp
/** @pred bdd_from_list(? _List_, ?_Vars_, - _BddHandle_) 

Convert a _List_ of logical expressions of the form above, that
includes the set of free variables _Vars_, into a BDD accessible
through _BddHandle_.

 
*/
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#false
cat << "EOF" > tmp
/** @pred bdd_eval(+ _BDDHandle_,  _Val_) 

Unify  _Val_ with the value of the logical expression compiled in
 _BDDHandle_ given an assignment to its  variables.

~~~~~
bdd_new(X+(Y+X)*(-Z), BDD), 
[X,Y,Z] = [0,0,0], 
bdd_eval(BDD, V), 
writeln(V).
~~~~~
would write 0 in the standard output stream.

The  Prolog code equivalent to <tt>bdd_eval/2</tt> is:

~~~~~
    Tree = bdd(1, T, _Vs),
    reverse(T, RT),
    foldl(eval_bdd, RT, _, V).

eval_bdd(pp(P,X,L,R), _, P) :-
    P is ( X/\L ) \/ ( (1-X) /\ R ).
eval_bdd(pn(P,X,L,R), _, P) :-
    P is ( X/\L ) \/ ( (1-X) /\ (1-R) ).
~~~~~
First, the nodes are reversed to implement bottom-up evaluation. Then,
we use the `foldl` list manipulation predicate to walk every node,
computing the disjunction of the two cases and binding the output
variable. The top node gives the full expression value. Notice that
`(1- _X_)`  implements negation.

 
*/
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#false
cat << "EOF" > tmp
/** @pred bdd_close( _BDDHandle_) 

close the BDD and release any resources it holds.




 */
EOF
sed -e "20r tmp" /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/bdd/bdd.yap

#true
cat << "EOF" > tmp
/** @pred chr_show_store(+ _Mod_)
Prints all suspended constraints of module  _Mod_ to the standard
output. This predicate is automatically called by the SWI-Prolog toplevel at
the end of each query for every CHR module currently loaded.  The prolog-flag
`chr_toplevel_show_store` controls whether the toplevel shows the
constraint stores. The value `true` enables it.  Any other value
disables it.




 */
EOF
sed -e "35r tmp" /Users/vsc/git/yap-6.3/packages/chr/chr_debug.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/chr/chr_debug.pl

#true
cat << "EOF" > tmp
/** @pred chr_notrace
De-activate the CHR tracer.  By default the CHR tracer is activated and
deactivated automatically by the Prolog predicates trace/0 and
notrace/0.

+ chr_leash/0 

Define the set of CHR ports on which the CHR
tracer asks for user intervention (i.e. stops).  _Spec_ is either a
list of ports or a predefined `alias`. Defined aliases are:
`full` to stop at all ports, `none` or `off` to never
stop, and `default` to stop at the `call`, `exit`,
`fail`, `wake` and `apply` ports.  See also leash/1.

 
*/
EOF
sed -e "74r tmp" /Users/vsc/git/yap-6.3/packages/chr/chr_runtime.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/chr/chr_runtime.pl

#true
cat << "EOF" > tmp
/** @pred wait(+ _PID_,- _Status_) 


Wait until process  _PID_ terminates, and return its exits  _Status_.




 */
EOF
sed -e "30r tmp" /Users/vsc/git/yap-6.3/packages/clib/unix.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clib/unix.pl

#true
cat << "EOF" > tmp
/** @pred kill( _Id_,+ _SIGNAL_) 



Send signal  _SIGNAL_ to process  _Id_. In Unix this predicate is
a direct interface to `kill` so one can send signals to groups of
processes. In WIN32 the predicate is an interface to
`TerminateProcess`, so it kills  _Id_ independently of  _SIGNAL_.

 
*/
EOF
sed -e "30r tmp" /Users/vsc/git/yap-6.3/packages/clib/unix.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clib/unix.pl

#true
cat << "EOF" > tmp
/** @pred minimize(<tt>V</tt>) 
minimise variable  _V_




 */
EOF
sed -e "108r tmp" /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl

#true
cat << "EOF" > tmp
/** @pred maximize( _V_)
maximise variable  _V_

 
*/
EOF
sed -e "108r tmp" /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl

#true
cat << "EOF" > tmp
/** @pred inf(+ _Expression_,- _Sup_)
Computes the supremum of  _Expression_ within the current state of
the constraint store and returns that supremum in  _Sup_. This
predicate does not change the constraint store.

 
*/
EOF
sed -e "108r tmp" /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl

#true
cat << "EOF" > tmp
/** @pred inf(+ _Expression_,- _Inf_)
Computes the infimum of  _Expression_ within the current state of the
constraint store and returns that infimum in  _Inf_. This predicate
does not change the constraint store.

 
*/
EOF
sed -e "108r tmp" /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl

#true
cat << "EOF" > tmp
/** @pred entailed(+ _Constraint_)
Succeeds if  _Constraint_ is necessarily true within the current
constraint store. This means that adding the negation of the constraint
to the store results in failure.

 
*/
EOF
sed -e "108r tmp" /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl

#true
cat << "EOF" > tmp
/** @pred dump(+ _Target_,+ _Newvars_,- _CodedAnswer_)
Returns the constraints on  _Target_ in the list  _CodedAnswer_
where all variables of  _Target_ have veen replaced by  _NewVars_.
This operation does not change the constraint store. E.g. in

~~~~~
dump([X,Y,Z],[x,y,z],Cons)
~~~~~

 _Cons_ will contain the constraints on  _X_,  _Y_ and
 _Z_ where these variables have been replaced by atoms `x`, `y` and `z`.




 */
EOF
sed -e "108r tmp" /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl

#true
cat << "EOF" > tmp
/** @pred bb_inf(+ _Ints_,+ _Expression_,- _Inf_,- _Vertext_,+ _Eps_)
Computes the infimum of  _Expression_ within the current constraint
store, with the additional constraint that in that infimum, all
variables in  _Ints_ have integral values.  _Vertex_ will contain
the values of  _Ints_ in the infimum.  _Eps_ denotes how much a
value may differ from an integer to be considered an integer. E.g. when
 _Eps_ = 0.001, then X = 4.999 will be considered as an integer (5 in
this case).  _Eps_ should be between 0 and 0.5.

 
*/
EOF
sed -e "108r tmp" /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl

#true
cat << "EOF" > tmp
/** @pred bb_inf(+ _Ints_,+ _Expression_,- _Inf_)
The same as bb_inf/5 but without returning the values of the integers
and with an eps of 0.001.

 
*/
EOF
sed -e "108r tmp" /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clpqr/clpr.pl

#true
cat << "EOF" > tmp
/** @pred split(+ _Line_,+ _Separators_,- _Split_) 



Unify  _Words_ with a set of strings obtained from  _Line_ by
using the character codes in  _Separators_ as separators. As an
example, consider:

~~~~~{.prolog}
?- split("Hello * I am free"," *",S).

S = ["Hello","I","am","free"] ?

no
~~~~~

 
*/
EOF
sed -e "59r tmp" /Users/vsc/git/yap-6.3/packages/clpqr/clpr/nf_r.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/clpqr/clpr/nf_r.pl

#true
cat << "EOF" > tmp
/** @pred minimum( _X_,  _Vs_)
 
*/
EOF
sed -e "30r tmp" /Users/vsc/git/yap-6.3/packages/gecode/clpfd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/gecode/clpfd.yap

#false
cat << "EOF" > tmp
/** @pred maximum( _X_,  _Vs_)
 
*/
EOF
sed -e "30r tmp" /Users/vsc/git/yap-6.3/packages/gecode/clpfd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/gecode/clpfd.yap

#false
cat << "EOF" > tmp
/** @pred element( _X_,  _Vs_    )
 _X_ is an element of list  _Vs_

 
*/
EOF
sed -e "30r tmp" /Users/vsc/git/yap-6.3/packages/gecode/clpfd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/gecode/clpfd.yap

#false
cat << "EOF" > tmp
/** @pred clause( _Type_,  _Ps_ ,  _Ns_,  _V_     )
If  _Type_ is `and` it is the conjunction of boolean variables
 _Ps_ and the negation of boolean variables  _Ns_ and must have
result  _V_. If  _Type_ is `or` it is a disjunction.

+ DFA
the interface allows creating and manipulation deterministic finite
automata. A DFA has a set of states, represented as integers
and is initialised with an initial state, a set of transitions from the
first to the last argument emitting the middle argument, and a final
state.

The swedish-drinkers protocol is represented as follows:

~~~~~{.prolog}
    A = [X,Y,Z],
    dfa( 0, [t(0,0,0),t(0,1,1),t(1,0,0),t(-1,0,0)], [0], C),
    in_dfa( A, C ),
~~~~~
This code will enumeratae the valid tuples of three emissions.

+ extensional constraints
Constraints can also be represented as lists of tuples. 

The previous example
would be written as:

~~~~~{.prolog}
    extensional_constraint([[0,0,0],[0,1,0],[1,0,0]], C),
    in_relation( A, C ),
~~~~~

 
*/
EOF
sed -e "30r tmp" /Users/vsc/git/yap-6.3/packages/gecode/clpfd.yap > x
     mv x /Users/vsc/git/yap-6.3/packages/gecode/clpfd.yap

#true
cat << "EOF" > tmp
/** @pred  primitive( _T_) 


Checks whether  _T_ is an atomic term or a database reference.

 
*/
EOF
sed -e "234r tmp" /Users/vsc/git/yap-6.3/packages/http/js_grammar.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/http/js_grammar.pl

#true
cat << "EOF" > tmp
/** @pred  _Term1_ =@=  _Term2_ is semidet



True iff  _Term1_ and  _Term2_ are structurally equivalent. I.e. if  _Term1_ and  _Term2_ are variants of each other.




 */
EOF
sed -e "43r tmp" /Users/vsc/git/yap-6.3/packages/plunit/swi.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/plunit/swi.pl

#true
cat << "EOF" > tmp
/** @pred  is_list(+ _List_) 


True when  _List_ is a proper list. That is,  _List_
is bound to the empty list (nil) or a term with functor '.' and arity 2.

 
*/
EOF
sed -e "83r tmp" /Users/vsc/git/yap-6.3/packages/xml/xml.lpa.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/xml/xml.lpa.pl

#true
cat << "EOF" > tmp
/** @pred  number_codes(? _A_,? _L_) is iso 


The predicate holds when at least one of the arguments is ground
(otherwise, an error message will be displayed). The argument  _A_
will be unified with a number and  _L_ with the list of the ASCII
codes for the characters of the external representation of  _A_.

 
*/
EOF
sed -e "51r tmp" /Users/vsc/git/yap-6.3/packages/xml/xml.lpa.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/xml/xml.lpa.pl

#true
cat << "EOF" > tmp
/** @pred  atom_codes(? _A_,? _L_) is iso 


The predicate holds when at least one of the arguments is ground
(otherwise, an error message will be displayed). The argument  _A_ will
be unified with an atom and  _L_ with the list of the ASCII
codes for the characters of the external representation of  _A_.

 
*/
EOF
sed -e "38r tmp" /Users/vsc/git/yap-6.3/packages/xml/xml.lpa.pl > x
     mv x /Users/vsc/git/yap-6.3/packages/xml/xml.lpa.pl

#false
cat << "EOF" > tmp
/** @pred  static_array_properties(? _Name_, ? _Size_, ? _Type_) 


Show the properties size and type of a static array with name
 _Name_. Can also be used to enumerate all current
static arrays. 

This built-in will silently fail if the there is no static array with
that name.

 
*/
EOF
sed -e "94r tmp" /Users/vsc/git/yap-6.3/pl/arrays.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/arrays.yap

#false
cat << "EOF" > tmp
/** @pred  array(+ _Name_, + _Size_) 


Creates a new dynamic array. The  _Size_ must evaluate to an
integer. The  _Name_ may be either an atom (named array) or an
unbound variable (anonymous array).

Dynamic arrays work as standard compound terms, hence space for the
array is recovered automatically on backtracking.

 
*/
EOF
sed -e "37r tmp" /Users/vsc/git/yap-6.3/pl/arrays.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/arrays.yap

#false
cat << "EOF" > tmp
/** @pred  current_atom( _A_) 


Checks whether  _A_ is a currently defined atom. It is used to find all
currently defined atoms by backtracking.

 
*/
EOF
sed -e "171r tmp" /Users/vsc/git/yap-6.3/pl/atoms.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/atoms.yap

#false
cat << "EOF" > tmp
/** @pred  atomic_list_concat(? _As_,+ _Separator_,? _A_)

Creates an atom just like atomic_list_concat/2, but inserts
 _Separator_ between each pair of atoms. For example:

~~~~~{.prolog}
?- atomic_list_concat([gnu, gnat], `, `, A).

A = `gnu, gnat`
~~~~~

YAP emulates the SWI-Prolog version of this predicate that can also be
used to split atoms by instantiating  _Separator_ and  _Atom_ as
shown below.

~~~~~{.prolog}
?- atomic_list_concat(L, -, 'gnu-gnat').

L = [gnu, gnat]
~~~~~

 
*/
EOF
sed -e "109r tmp" /Users/vsc/git/yap-6.3/pl/atoms.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/atoms.yap

#true
cat << "EOF" > tmp
/** @pred  atomic_list_concat(+ _As_,? _A_) 


The predicate holds when the first argument is a list of atomic terms, and
the second unifies with the atom obtained by concatenating all the
atomic terms in the first list. The first argument thus may contain
atoms or numbers.

 
*/
EOF
sed -e "83r tmp" /Users/vsc/git/yap-6.3/pl/atoms.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/atoms.yap

#false
cat << "EOF" > tmp
/** @pred  atom_concat(+ _As_,? _A_) 


The predicate holds when the first argument is a list of atoms, and the
second unifies with the atom obtained by concatenating all the atoms in
the first list.

 
*/
EOF
sed -e "33r tmp" /Users/vsc/git/yap-6.3/pl/atoms.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/atoms.yap

#false
cat << "EOF" > tmp
/** @pred call_residue(: _G_, _L_) 



Call goal  _G_. If subgoals of  _G_ are still blocked, return
a list containing these goals and the variables they are blocked in. The
goals are then considered as unblocked. The next example shows a case
where dif/2 suspends twice, once outside call_residue/2,
and the other inside:

~~~~~
?- dif(X,Y),
       call_residue((dif(X,Y),(X = f(Z) ; Y = f(Z))), L).

X = f(Z),
L = [[Y]-dif(f(Z),Y)],
dif(f(Z),Y) ? ;

Y = f(Z),
L = [[X]-dif(X,f(Z))],
dif(X,f(Z)) ? ;

no
~~~~~
The system only reports one invocation of dif/2 as having
suspended. 

 
*/
EOF
sed -e "498r tmp" /Users/vsc/git/yap-6.3/pl/attributes.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/attributes.yap

#false
cat << "EOF" > tmp
/** @pred call_residue_vars(: _G_, _L_) 



Call goal  _G_ and unify  _L_ with a list of all constrained variables created <em>during</em> execution of  _G_:

~~~~~
  ?- dif(X,Z), call_residue_vars(dif(X,Y),L).
dif(X,Z), call_residue_vars(dif(X,Y),L).
L = [Y],
dif(X,Z),
dif(X,Y) ? ;

no
~~~~~




 */
EOF
sed -e "393r tmp" /Users/vsc/git/yap-6.3/pl/attributes.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/attributes.yap

#true
cat << "EOF" > tmp
/** @pred copy_term(? _TI_,- _TF_,- _Goals_) 

Term  _TF_ is a variant of the original term  _TI_, such that for
each variable  _V_ in the term  _TI_ there is a new variable  _V'_
in term  _TF_ without any attributes attached.  Attributed
variables are thus converted to standard variables.   _Goals_ is
unified with a list that represents the attributes.  The goal
`maplist(call, _Goals_)` can be called to recreate the
attributes.

Before the actual copying, `copy_term/3` calls
`attribute_goals/1` in the module where the attribute is
defined.

 
*/
EOF
sed -e "249r tmp" /Users/vsc/git/yap-6.3/pl/attributes.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/attributes.yap

#false
cat << "EOF" > tmp
/** @pred put_attrs(+ _Var_,+ _Attributes_) 


Set all attributes of  _Var_.  See get_attrs/2 for a description of
 _Attributes_.

 
*/
EOF
sed -e "223r tmp" /Users/vsc/git/yap-6.3/pl/attributes.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/attributes.yap

#false
cat << "EOF" > tmp
/** @pred del_attrs(+ _Var_) 


If  _Var_ is an attributed variable, delete <em>all</em> its
attributes.  In all other cases, this predicate succeeds without
side-effects.

 
*/
EOF
sed -e "209r tmp" /Users/vsc/git/yap-6.3/pl/attributes.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/attributes.yap

#false
cat << "EOF" > tmp
/** @pred del_attr(+ _Var_,+ _Module_) 



Delete the named attribute.  If  _Var_ loses its last attribute it
is transformed back into a traditional Prolog variable.  If  _Module_
is not an atom, a type error is raised. In all other cases this
predicate succeeds regardless whether or not the named attribute is
present.

 
*/
EOF
sed -e "196r tmp" /Users/vsc/git/yap-6.3/pl/attributes.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/attributes.yap

#false
cat << "EOF" > tmp
/** @pred get_attr(+ _Var_,+ _Module_,- _Value_) 



Request the current  _value_ for the attribute named  _Module_.  If
 _Var_ is not an attributed variable or the named attribute is not
associated to  _Var_ this predicate fails silently.  If  _Module_
is not an atom, a type error is raised.

 
*/
EOF
sed -e "160r tmp" /Users/vsc/git/yap-6.3/pl/attributes.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/attributes.yap

#false
cat << "EOF" > tmp
/** @pred  throw(+ _Ball_) is iso 


The goal `throw( _Ball_)` throws an exception. Execution is
stopped, and the exception is sent to the ancestor goals until reaching
a matching catch/3, or until reaching top-level.

 
*/
EOF
sed -e "1534r tmp" /Users/vsc/git/yap-6.3/pl/boot.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/boot.yap

#false
cat << "EOF" > tmp
/** @pred  catch( : _Goal_,+ _Exception_,+ _Action_) is iso 


The goal `catch( _Goal_, _Exception_, _Action_)` tries to
execute goal  _Goal_. If during its execution,  _Goal_ throws an
exception  _E'_ and this exception unifies with  _Exception_, the
exception is considered to be caught and  _Action_ is executed. If
the exception  _E'_ does not unify with  _Exception_, control
again throws the exception.

The top-level of YAP maintains a default exception handler that
is responsible to capture uncaught exceptions.

 
*/
EOF
sed -e "1497r tmp" /Users/vsc/git/yap-6.3/pl/boot.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/boot.yap

#false
cat << "EOF" > tmp
/** @pred  expand_term( _T_,- _X_) 



This predicate is used by YAP for preprocessing each top level
term read when consulting a file and before asserting or executing it.
It rewrites a term  _T_ to a term  _X_ according to the following
rules: first try term_expansion/2  in the current module, and then try to use the user defined predicate
`user:term_expansion/2`. If this call fails then the translating process
for DCG rules is applied, together with the arithmetic optimizer
whenever the compilation of arithmetic expressions is in progress.

 
*/
EOF
sed -e "1452r tmp" /Users/vsc/git/yap-6.3/pl/boot.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/boot.yap

#false
cat << "EOF" > tmp
/** @pred  incore(+ _P_) 


The same as call/1.

 
*/
EOF
sed -e "1119r tmp" /Users/vsc/git/yap-6.3/pl/boot.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/boot.yap

#false
cat << "EOF" > tmp
/** @pred  call(+ _P_) is iso 
Meta-call predicate.

If _P_ is instantiated to an atom or a compound term, the goal `call(
_P_)` is executed as if the clause was originally written as _P_
instead as call( _P_ ), except that any "cut" occurring in _P_ only
cuts alternatives in the execution of _P_.

 
*/
EOF
sed -e "1110r tmp" /Users/vsc/git/yap-6.3/pl/boot.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/boot.yap

#false
cat << "EOF" > tmp
/** @pred  repeat is iso 
Succeeds repeatedly.

In the next example, `repeat` is used as an efficient way to implement
a loop. The next example reads all terms in a file:
~~~~~~~~~~~~~{.prolog}
 a :- repeat, read(X), write(X), nl, X=end_of_file, !.
~~~~~~~~~~~~~
the loop is effectively terminated by the cut-goal, when the test-goal
`X=end` succeeds. While the test fails, the goals `read(X)`,
`write(X)`, and `nl` are executed repeatedly, because
backtracking is caught by the `repeat` goal.

The built-in `repeat/0` could be defined in Prolog by:

~~~~~{.prolog}
 repeat.
 repeat :- repeat.
~~~~~

The predicate between/3 can be used to iterate for a pre-defined
number of steps.
 
*/
EOF
sed -e "583r tmp" /Users/vsc/git/yap-6.3/pl/boot.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/boot.yap

#false
cat << "EOF" > tmp
/** @pred  true is iso 


Succeeds once.

 
*/
EOF
sed -e "299r tmp" /Users/vsc/git/yap-6.3/pl/boot.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/boot.yap

#false
cat << "EOF" > tmp
/** @pred  call_count(? _CallsMax_, ? _RetriesMax_, ? _CallsAndRetriesMax_) 


Set call counters as timers. YAP will generate an exception
if one of the instantiated call counters decreases to 0:

+ _CallsMax_

    throw the exception `call_counter` when the
counter `calls` reaches 0;

+ _RetriesMax_

    throw the exception `retry_counter` when the
counter `retries` reaches 0;

+ _CallsAndRetriesMax_

    throw the exception
`call_and_retry_counter` when the counter `calls_and_retries`
reaches 0.

 YAP will ignore counters that are called with unbound arguments.

Next, we show a simple example of how to use call counters:

~~~~~{.prolog}
   ?- yap_flag(call_counting,on), [-user]. l :- l. end_of_file. yap_flag(call_counting,off).

yes

yes
   ?- catch((call_count(10000,_,_),l),call_counter,format("limit_exceeded.~n",[])).

limit_exceeded.

yes
~~~~~
Notice that we first compile the looping predicate `l/0` with
call_counting `on`. Next, we catch/3 to handle an
exception when `l/0` performs more than 10000 reductions.


 */
EOF
sed -e "142r tmp" /Users/vsc/git/yap-6.3/pl/callcount.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/callcount.yap

#false
cat << "EOF" > tmp
/** @pred  call_count_reset 


Reset call count counters. All timers are also reset.

*/
EOF
sed -e "95r tmp" /Users/vsc/git/yap-6.3/pl/callcount.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/callcount.yap

#false
cat << "EOF" > tmp
/** @pred  call_count_data(- _Calls_, - _Retries_, - _CallsAndRetries_) 


Give current call count data. The first argument gives the current value
for the  _Calls_ counter, next the  _Retries_ counter, and last
the  _CallsAndRetries_ counter.
 
*/
EOF
sed -e "86r tmp" /Users/vsc/git/yap-6.3/pl/callcount.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/callcount.yap

#false
cat << "EOF" > tmp
/** @pred prolog_load_context(? _Key_, ? _Value_) 


Obtain information on what is going on in the compilation process. The
following keys are available:



+ directory 



Full name for the directory where YAP is currently consulting the
file.

+ file 



Full name for the file currently being consulted. Notice that included
filed are ignored.

+ module 



Current source module.

+ `source` (prolog_load_context/2 option) 

    Full name for the file currently being read in, which may be consulted,
reconsulted, or included.

+ `stream` 

    Stream currently being read in.

+ `term_position` 

    Stream position at the stream currently being read in. For SWI
compatibility, it is a term of the form
'$stream_position'(0,Line,0,0,0).


+ `source_location(? _FileName_, ? _Line_)` 

    SWI-compatible predicate. If the last term has been read from a physical file (i.e., not from the file user or a string), unify File with an absolute path to the file and Line with the line-number in the file. Please use prolog_load_context/2.

+ `source_file(? _File_)`

    SWI-compatible predicate. True if  _File_ is a loaded Prolog source file.

+ `source_file(? _ModuleAndPred_,? _File_)`

    SWI-compatible predicate. True if the predicate specified by  _ModuleAndPred_ was loaded from file  _File_, where  _File_ is an absolute path name (see `absolute_file_name/2`).



@section YAPLibrary Library Predicates

Library files reside in the library_directory path (set by the
`LIBDIR` variable in the Makefile for YAP). Currently,
most files in the library are from the Edinburgh Prolog library. 


 */
EOF
sed -e "958r tmp" /Users/vsc/git/yap-6.3/pl/consult.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/consult.yap

#false
cat << "EOF" > tmp
/** @pred  halt(+  _I_) is iso

Halts Prolog, and exits to the calling application returning the code
given by the integer  _I_.

 
*/
EOF
sed -e "732r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  halt is iso 


Halts Prolog, and exits to the calling application. In YAP,
halt/0 returns the exit code `0`.

 
*/
EOF
sed -e "719r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  break 


Suspends the execution of the current goal and creates a new execution
level similar to the top level, displaying the following message:

~~~~~{.prolog}
 [ Break (level <number>) ]
~~~~~
telling the depth of the break level just entered. To return to the
previous level just type the end-of-file character or call the
end_of_file predicate.  This predicate is especially useful during
debugging.

 
*/
EOF
sed -e "677r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred b_getval(+ _Name_,- _Value_) 


Get the value associated with the global variable  _Name_ and unify
it with  _Value_. Note that this unification may further instantiate
the value of the global variable. If this is undesirable the normal
precautions (double negation or copy_term/2) must be taken. The
b_getval/2 predicate generates errors if  _Name_ is not an atom or
the requested variable does not exist.

 
*/
EOF
sed -e "618r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  b_getval(+ _Name_, - _Value_)  


Get the value associated with the global variable  _Name_ and unify
it with  _Value_. Note that this unification may further
instantiate the value of the global variable. If this is undesirable
the normal precautions (double negation or copy_term/2) must be
taken. The b_getval/2 predicate generates errors if  _Name_ is not
an atom or the requested variable does not exist. 

Notice that for compatibility with other systems  _Name_ <em>must</em> be already associated with a term: otherwise the system will generate an error.

 
*/
EOF
sed -e "618r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred nb_getval(+ _Name_,- _Value_) 


The nb_getval/2 predicate is a synonym for b_getval/2, introduced for
compatibility and symmetry.  As most scenarios will use a particular
global variable either using non-backtrackable or backtrackable
assignment, using nb_getval/2 can be used to document that the 
variable is used non-backtrackable.

 
*/
EOF
sed -e "579r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  nb_getval(+ _Name_, - _Value_)  


The nb_getval/2 predicate is a synonym for b_getval/2,
introduced for compatibility and symmetry. As most scenarios will use
a particular global variable either using non-backtrackable or
backtrackable assignment, using nb_getval/2 can be used to
document that the variable is used non-backtrackable.

 
*/
EOF
sed -e "579r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#true
cat << "EOF" > tmp
/** @pred version(- _Message_)

Add a message to be written when yap boots or after aborting. It is not
possible to remove messages.

 
*/
EOF
sed -e "539r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred version

Write YAP's boot message. 

 
*/
EOF
sed -e "530r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred prolog_initialization( _G_) 


Add a goal to be executed on system initialization. This is compatible
with SICStus Prolog's initialization/1.

 
*/
EOF
sed -e "514r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  garbage_collect_atoms 


The goal `garbage_collect` forces a garbage collection of the atoms
in the data-base. Currently, only atoms are recovered.

 
*/
EOF
sed -e "492r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  nogc 


The goal `nogc` disables garbage collection. The same as
`yap_flag(gc,off)`.

 
*/
EOF
sed -e "480r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  gc 


The goal `gc` enables garbage collection. The same as
`yap_flag(gc,on)`.

 
*/
EOF
sed -e "470r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  garbage_collect 


The goal `garbage_collect` forces a garbage collection.

 
*/
EOF
sed -e "457r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  grow_stack(+ _Size_) 


Increase stack size  _Size_ kilobytes


 */
EOF
sed -e "443r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  grow_heap(+ _Size_) 
Increase heap size  _Size_ kilobytes.

 
*/
EOF
sed -e "435r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred setup_call_catcher_cleanup(: _Setup_,: _Goal_, + _Catcher_,: _CleanUpGoal_) 


Similar to `setup_call_cleanup( _Setup_,  _Goal_,  _Cleanup_)` with
additional information on the reason of calling  _Cleanup_.  Prior
to calling  _Cleanup_,  _Catcher_ unifies with the termination
code.  If this unification fails,  _Cleanup_ is
 *not* called.

 
*/
EOF
sed -e "326r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred setup_call_cleanup(: _Setup_,: _Goal_, : _CleanUpGoal_) 


Calls `(Setup, Goal)`. For each sucessful execution of  _Setup_, calling  _Goal_, the
cleanup handler  _Cleanup_ is guaranteed to be called exactly once.
This will happen after  _Goal_ completes, either through failure,
deterministic success, commit, or an exception.   _Setup_ will
contain the goals that need to be protected from asynchronous interrupts
such as the ones received from `call_with_time_limit/2` or thread_signal/2.  In
most uses,  _Setup_ will perform temporary side-effects required by
 _Goal_ that are finally undone by  _Cleanup_.

Success or failure of  _Cleanup_ is ignored and choice-points it
created are destroyed (as once/1). If  _Cleanup_ throws an exception,
this is executed as normal.

Typically, this predicate is used to cleanup permanent data storage
required to execute  _Goal_, close file-descriptors, etc. The example
below provides a non-deterministic search for a term in a file, closing
the stream as needed.

~~~~~{.prolog}
term_in_file(Term, File) :-
    setup_call_cleanup(open(File, read, In),
               term_in_stream(Term, In),
               close(In) ).

term_in_stream(Term, In) :-
    repeat,
    read(In, T),
    (   T == end_of_file
    ->  !, fail
    ;   T = Term
    ).
~~~~~

Note that it is impossible to implement this predicate in Prolog other than
by reading all terms into a list, close the file and call member/2.
Without setup_call_cleanup/3 there is no way to gain control if the
choice-point left by `repeat` is removed by a cut or an exception.

`setup_call_cleanup/2` can also be used to test determinism of a goal:

~~~~~
?- setup_call_cleanup(true,(X=1;X=2), Det=yes).

X = 1 ;

X = 2,
Det = yes ;
~~~~~

This predicate is under consideration for inclusion into the ISO standard.
For compatibility with other Prolog implementations see `call_cleanup/2`.

 
*/
EOF
sed -e "312r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#true
cat << "EOF" > tmp
/** @pred call_cleanup(: _Goal_, : _CleanUpGoal_)

This is similar to <tt>call_cleanup/1</tt> with an additional
 _CleanUpGoal_ which gets called after  _Goal_ is finished.

 
*/
EOF
sed -e "249r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  call(+ _Closure_,...,? _Ai_,...) is iso 


Meta-call where  _Closure_ is a closure that is converted into a goal by 
appending the  _Ai_ additional arguments. The number of arguments varies 
between 0 and 10.

 
*/
EOF
sed -e "224r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  if(? _G_,? _H_,? _I_)

Call goal  _H_ once per each solution of goal  _H_. If goal
 _H_ has no solutions, call goal  _I_.

The built-in `if/3` is similar to `->/3`, with the difference
that it will backtrack over the test goal. Consider the following
small data-base:

~~~~~{.prolog}
a(1).        b(a).          c(x).
a(2).        b(b).          c(y).
~~~~~

Execution of an `if/3` query will proceed as follows:

~~~~~{.prolog}
   ?- if(a(X),b(Y),c(Z)).

X = 1,
Y = a ? ;

X = 1,
Y = b ? ;

X = 2,
Y = a ? ;

X = 2,
Y = b ? ;

no
~~~~~

The system will backtrack over the two solutions for `a/1` and the
two solutions for `b/1`, generating four solutions.

Cuts are allowed inside the first goal  _G_, but they will only prune
over  _G_.

If you want  _G_ to be deterministic you should use if-then-else, as
it is both more efficient and more portable.

 
*/
EOF
sed -e "200r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#true
cat << "EOF" > tmp
/** @pred  ignore(: _Goal_) 


Calls  _Goal_ as once/1, but succeeds, regardless of whether
`Goal` succeeded or not. Defined as:

~~~~~{.prolog}
ignore(Goal) :-
        Goal, !.
ignore(_).
~~~~~

 
*/
EOF
sed -e "141r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#true
cat << "EOF" > tmp
/** @pred forall(+ _Cond_,+ _Action_) 




For all alternative bindings of  _Cond_  _Action_ can be proven.
The next example verifies that all arithmetic statements in the list
 _L_ are correct. It does not say which is wrong if one proves wrong.

~~~~~
?- forall(member(Result = Formula, [2 = 1 + 1, 4 = 2 * 2]),
                 Result =:= Formula).
~~~~~



*/
EOF
sed -e "125r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#true
cat << "EOF" > tmp
/** @pred  forall(: _Cond_,: _Action_) 


For all alternative bindings of  _Cond_  _Action_ can be
proven. The example verifies that all arithmetic statements in the list
 _L_ are correct. It does not say which is wrong if one proves wrong.

~~~~~{.prolog}
?- forall(member(Result = Formula, [2 = 1 + 1, 4 = 2 * 2]),
                 Result =:= Formula).
~~~~~

 
*/
EOF
sed -e "125r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred  once(: _G_) is iso 


Execute the goal  _G_ only once. The predicate is defined by:

~~~~~{.prolog}
 once(G) :- call(G), !.
~~~~~

Note that cuts inside once/1 can only cut the other goals inside
once/1.

 
*/
EOF
sed -e "92r tmp" /Users/vsc/git/yap-6.3/pl/control.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/control.yap

#false
cat << "EOF" > tmp
/** @pred frozen( _X_, _G_) 


Unify  _G_ with a conjunction of goals suspended on variable  _X_,
or `true` if no goal has suspended.

 
*/
EOF
sed -e "572r tmp" /Users/vsc/git/yap-6.3/pl/corout.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/corout.yap

#false
cat << "EOF" > tmp
/** @pred when(+ _C_,: _G_) 


Delay execution of goal  _G_ until the conditions  _C_ are
satisfied. The conditions are of the following form:

+ _C1_, _C2_
Delay until both conditions  _C1_ and  _C2_ are satisfied.
+ _C1_; _C2_
Delay until either condition  _C1_ or condition  _C2_ is satisfied.
+ ?=( _V1_, _C2_)
Delay until terms  _V1_ and  _V1_ have been unified.
+ nonvar( _V_)
Delay until variable  _V_ is bound.
+ ground( _V_)
Delay until variable  _V_ is ground.


Note that when/2 will fail if the conditions fail.

 
*/
EOF
sed -e "331r tmp" /Users/vsc/git/yap-6.3/pl/corout.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/corout.yap

#false
cat << "EOF" > tmp
/** @pred dif( _X_, _Y_) 


Succeed if the two arguments do not unify. A call to dif/2 will
suspend if unification may still succeed or fail, and will fail if they
always unify.

 
*/
EOF
sed -e "232r tmp" /Users/vsc/git/yap-6.3/pl/corout.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/corout.yap

#false
cat << "EOF" > tmp
/** @pred freeze(? _X_,: _G_) 


Delay execution of goal  _G_ until the variable  _X_ is bound.

 
*/
EOF
sed -e "171r tmp" /Users/vsc/git/yap-6.3/pl/corout.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/corout.yap

#true
cat << "EOF" > tmp
/** @pred attribute_goals(+ _Var_,- _Gs_,+ _GsRest_) 



This nonterminal, if it is defined in a module, is used by  _copy_term/3_
to project attributes of that module to residual goals. It is also
used by the toplevel to obtain residual goals after executing a query.


Normal user code should deal with put_attr/3, get_attr/3 and del_attr/2.
The routines in this section fetch or set the entire attribute list of a
variables. Use of these predicates is anticipated to be restricted to
printing and other special purpose operations.



 @pred get_attrs(+ _Var_,- _Attributes_) 



Get all attributes of  _Var_.  _Attributes_ is a term of the form
`att( _Module_,  _Value_,  _MoreAttributes_)`, where  _MoreAttributes_ is
`[]` for the last attribute.

 
*/
EOF
sed -e "133r tmp" /Users/vsc/git/yap-6.3/pl/corout.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/corout.yap

#true
cat << "EOF" > tmp
/** @pred attr_unify_hook(+ _AttValue_,+ _VarValue_) 



Hook that must be defined in the module an attributed variable refers
to. Is is called <em>after</em> the attributed variable has been
unified with a non-var term, possibly another attributed variable.
 _AttValue_ is the attribute that was associated to the variable
in this module and  _VarValue_ is the new value of the variable.
Normally this predicate fails to veto binding the variable to
 _VarValue_, forcing backtracking to undo the binding.  If
 _VarValue_ is another attributed variable the hook often combines
the two attribute and associates the combined attribute with
 _VarValue_ using put_attr/3.

 
*/
EOF
sed -e "87r tmp" /Users/vsc/git/yap-6.3/pl/corout.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/corout.yap

#false
cat << "EOF" > tmp
/** @pred leash(+ _M_) 


Sets leashing mode to  _M_.
The mode can be specified as:

+ `full`
prompt on Call, Exit, Redo and Fail

+ `tight`
prompt on Call, Redo and Fail

+ `half`
prompt on Call and Redo

+ `loose`
prompt on Call

+ `off`
never prompt

+ `none`
never prompt, same as `off`

The initial leashing mode is `full`.

The user may also specify directly the debugger ports 
where he wants to be prompted. If the argument for leash 
is a number  _N_, each of lower four bits of the number is used to
control prompting at one the ports of the box model. The debugger will 
prompt according to the following conditions:

+ if `N/\ 1 =\= 0`  prompt on fail 
+ if `N/\ 2 =\= 0` prompt on redo
+ if `N/\ 4 =\= 0` prompt on exit
+ if `N/\ 8 =\= 0` prompt on call

Therefore, `leash(15)` is equivalent to `leash(full)` and
`leash(0)` is equivalent to `leash(off)`.

Another way of using `leash` is to give it a list with the names of
the ports where the debugger should stop. For example,
`leash([call,exit,redo,fail])` is the same as `leash(full)` or
`leash(15)` and `leash([fail])` might be used instead of
`leash(1)`.

 
*/
EOF
sed -e "348r tmp" /Users/vsc/git/yap-6.3/pl/debug.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/debug.yap

#false
cat << "EOF" > tmp
/** @pred notrace 


Ends tracing and exits the debugger. This is the same as
nodebug/0.




 */
EOF
sed -e "288r tmp" /Users/vsc/git/yap-6.3/pl/debug.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/debug.yap

#false
cat << "EOF" > tmp
/** @pred trace 


Switches on the debugger and enters tracing mode.

 
*/
EOF
sed -e "269r tmp" /Users/vsc/git/yap-6.3/pl/debug.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/debug.yap

#false
cat << "EOF" > tmp
/** @pred nospyall 


Removes all existing spy-points.

 
*/
EOF
sed -e "227r tmp" /Users/vsc/git/yap-6.3/pl/debug.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/debug.yap

#false
cat << "EOF" > tmp
/** @pred nospy( + _P_ )


Removes spy-points from all predicates specified by  _P_.
The possible forms for  _P_ are the same as in `spy P`.

 
*/
EOF
sed -e "212r tmp" /Users/vsc/git/yap-6.3/pl/debug.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/debug.yap

#false
cat << "EOF" > tmp
/** @pred spy( + _P_ ). 


Sets spy-points on all the predicates represented by
 _P_.  _P_ can either be a single specification or a list of 
specifications. Each one must be of the form  _Name/Arity_ 
or  _Name_. In the last case all predicates with the name 
 _Name_ will be spied. As in C-Prolog, system predicates and 
predicates written in C, cannot be spied.

 
*/
EOF
sed -e "196r tmp" /Users/vsc/git/yap-6.3/pl/debug.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/debug.yap

#false
cat << "EOF" > tmp
/** @pred print_message(+ _Kind_,  _Term_) 

The predicate print_message/2 is used to print messages, notably from
exceptions in a human-readable format.  _Kind_ is one of
`informational`, `banner`, `warning`, `error`,
`help` or `silent`. A human-readable message is printed to
the stream user_error.

If the Prolog flag verbose is `silent`, messages with
 _Kind_ `informational`, or `banner` are treated as
silent.@c  See \cmdlineoption{-q}.

This predicate first translates the  _Term_ into a list of `message
lines` (see print_message_lines/3 for details).  Next it will
call the hook message_hook/3 to allow the user intercepting the
message.  If message_hook/3 fails it will print the message unless
 _Kind_ is silent.

If you need to report errors from your own predicates, we advise you to
stick to the existing error terms if you can; but should you need to
invent new ones, you can define corresponding error messages by
asserting clauses for `prolog:message/2`. You will need to declare
the predicate as multifile.

 
*/
EOF
sed -e "297r tmp" /Users/vsc/git/yap-6.3/pl/errors.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/errors.yap

#false
cat << "EOF" > tmp
/** @pred  message_to_string(+ _Term_, - _String_) 


Translates a message-term into a string object. Primarily intended for SWI-Prolog emulation.



 */
EOF
sed -e "268r tmp" /Users/vsc/git/yap-6.3/pl/errors.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/errors.yap

#false
cat << "EOF" > tmp
/** @pred create_prolog_flag(+ _Flag_,+ _Value_,+ _Options_) 



Create a new YAP Prolog flag.  _Options_ include `type(+Type)` and `access(+Access)` with  _Access_
one of `read_only` or `read_write` and  _Type_ one of `boolean`, `integer`, `float`, `atom`
and `term` (that is, no type).

 
*/
EOF
sed -e "1343r tmp" /Users/vsc/git/yap-6.3/pl/flags.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/flags.yap

#false
cat << "EOF" > tmp
/** @pred prolog_flag(? _Flag_,- _OldValue_,+ _NewValue_) 



Obtain the value for a YAP Prolog flag and then set it to a new
value. Equivalent to first calling current_prolog_flag/2 with the
second argument  _OldValue_ unbound and then calling
set_prolog_flag/2 with the third argument  _NewValue_.

 
*/
EOF
sed -e "1323r tmp" /Users/vsc/git/yap-6.3/pl/flags.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/flags.yap

#false
cat << "EOF" > tmp
/** @pred set_prolog_flag(+ _Flag_,+ _Value_) is iso 



Set the value for YAP Prolog flag `Flag`. Equivalent to
calling yap_flag/2 with both arguments bound.

 
*/
EOF
sed -e "1280r tmp" /Users/vsc/git/yap-6.3/pl/flags.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/flags.yap

#false
cat << "EOF" > tmp
/** @pred current_prolog_flag(? _Flag_,- _Value_) is iso 

Obtain the value for a YAP Prolog flag. Equivalent to calling
yap_flag/2 with the second argument unbound, and unifying the
returned second argument with  _Value_.

 
*/
EOF
sed -e "1256r tmp" /Users/vsc/git/yap-6.3/pl/flags.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/flags.yap

#false
cat << "EOF" > tmp
/** @pred yap_flag(tabling_mode,? _Mode_)
Sets or reads the tabling mode for all tabled predicates. The list of
 _Mode_ options includes:

+ `default`

    Defines that (i) all calls to tabled predicates are evaluated
using the predicate default mode, and that (ii) answers for all
completed calls are obtained by using the predicate default mode.

+ `batched`

    Defines that all calls to tabled predicates are evaluated using
batched scheduling. This option ignores the default tabling mode
of each predicate.

+ `local`

    Defines that all calls to tabled predicates are evaluated using
local scheduling. This option ignores the default tabling mode
of each predicate.

+ `exec_answers`

    Defines that answers for all completed calls are obtained by
executing compiled WAM-like code directly from the trie data
structure. This option ignores the default tabling mode
of each predicate.

+ `load_answers`

    Defines that answers for all completed calls are obtained by
loading them from the trie data structure. This option ignores
the default tabling mode of each predicate.


 
*/
EOF
sed -e "585r tmp" /Users/vsc/git/yap-6.3/pl/flags.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/flags.yap

#false
cat << "EOF" > tmp
/** @pred  yap_flag(unknown,+ _SPEC_) 

Alternatively, one can use yap_flag/2,
current_prolog_flag/2, or set_prolog_flag/2, to set this
functionality. In this case, the first argument for the built-ins should
be `unknown`, and the second argument should be either
`error`, `warning`, `fail`, or a goal.

 
*/
EOF
sed -e "585r tmp" /Users/vsc/git/yap-6.3/pl/flags.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/flags.yap

#false
cat << "EOF" > tmp
/** @pred  yap_flag(? _Param_,? _Value_) 


Set or read system properties for  _Param_:


+ `argv `

    Read-only flag. It unifies with a list of atoms that gives the
arguments to YAP after `--`.

+ `agc_margin `

    An integer: if this amount of atoms has been created since the last
atom-garbage collection, perform atom garbage collection at the first
opportunity. Initial value is 10,000. May be changed. A value of 0
(zero) disables atom garbage collection.

+ `associate `

    Read-write flag telling a suffix for files associated to Prolog
sources. It is `yap` by default.

+ `bounded is iso `

    Read-only flag telling whether integers are bounded. The value depends
on whether YAP uses the GMP library or not.

+ `profiling `

    If `off` (default) do not compile call counting information for
procedures. If `on` compile predicates so that they calls and
retries to the predicate may be counted. Profiling data can be read through the
call_count_data/3 built-in.

+ `char_conversion is iso`

    Writable flag telling whether a character conversion table is used when
reading terms. The default value for this flag is `off` except in
`sicstus` and `iso` language modes, where it is `on`.

+ `character_escapes is iso `

    Writable flag telling whether a character escapes are enables,
`true`, or disabled, `false`. The default value for this flag is
`on`.

+ `debug is iso `

    If  _Value_ is unbound, tell whether debugging is `true` or
`false`. If  _Value_ is bound to `true` enable debugging, and if
it is bound to `false` disable debugging.

+ `debugger_print_options `

    If bound, set the argument to the `write_term/3` options the
debugger uses to write terms. If unbound, show the current options.

+ `dialect `

    Read-only flag that always returns `yap`.

+ `discontiguous_warnings `

    If  _Value_ is unbound, tell whether warnings for discontiguous
predicates are `on` or
`off`. If  _Value_ is bound to `on` enable these warnings,
and if it is bound to `off` disable them. The default for YAP is
`off`, unless we are in `sicstus` or `iso` mode.

+ `dollar_as_lower_case `

    If `off` (default)  consider the character `$` a control character, if
`on` consider `$` a lower case character.

+ `double_quotes is iso `

    If  _Value_ is unbound, tell whether a double quoted list of characters
token is converted to a list of atoms, `chars`, to a list of integers,
`codes`, or to a single atom, `atom`. If  _Value_ is bound, set to
the corresponding behavior. The default value is `codes`.

+ `executable `

    Read-only flag. It unifies with an atom that gives the
original program path.

+ `fast `

    If `on` allow fast machine code, if `off` (default) disable it. Only
available in experimental implementations.

+ `fileerrors`

    If `on` `fileerrors` is `on`, if `off` (default)
`fileerrors` is disabled.

+ `float_format `

    C-library `printf()` format specification used by write/1 and
friends to determine how floating point numbers are printed. The
default is `%.15g`. The specified value is passed to `printf()`
without further checking. For example, if you want less digits
printed, `%g` will print all floats using 6 digits instead of the
default 15.

+ `gc`

    If `on` allow garbage collection (default), if `off` disable it.

+ `gc_margin `

    Set or show the minimum free stack before starting garbage
collection. The default depends on total stack size. 

+ `gc_trace `

    If `off` (default) do not show information on garbage collection
and stack shifts, if `on` inform when a garbage collection or stack
shift happened, if verbose give detailed information on garbage
collection and stack shifts. Last, if `very_verbose` give detailed
information on data-structures found during the garbage collection
process, namely, on choice-points.

+ `generate_debugging_info `

    If `true` (default) generate debugging information for
procedures, including source mode. If `false` predicates no
information is generated, although debugging is still possible, and
source mode is disabled.

+ `host_type `

    Return `configure` system information, including the machine-id
for which YAP was compiled and Operating System information. 

+ `index `

    If `on` allow indexing (default), if `off` disable it, if
`single` allow on first argument only.

+ `index_sub_term_search_depth `

    Maximum bound on searching sub-terms for indexing, if `0` (default) no bound.

+ `informational_messages `

    If `on` allow printing of informational messages, such as the ones
that are printed when consulting. If `off` disable printing
these messages. It is `on` by default except if YAP is booted with
the `-L` flag.

+ `integer_rounding_function is iso `

    Read-only flag telling the rounding function used for integers. Takes the value
`toward_zero` for the current version of YAP.

+ `language `

    Choose whether YAP is closer to C-Prolog, `cprolog`, iso-prolog,
`iso` or SICStus Prolog, `sicstus`. The current default is
`cprolog`. This flag affects update semantics, leashing mode,
style checking, handling calls to undefined procedures, how directives
are interpreted, when to use dynamic, character escapes, and how files
are consulted.

+ `max_arity is iso `

    Read-only flag telling the maximum arity of a functor. Takes the value
`unbounded` for the current version of YAP.

+ `max_integer is iso `

    Read-only flag telling the maximum integer in the
implementation. Depends on machine and Operating System
architecture, and on whether YAP uses the `GMP` multi-precision
library. If bounded is false, requests for max_integer
will fail.

+ `max_tagged_integer  `

    Read-only flag telling the maximum integer we can store as a single
word. Depends on machine and Operating System
architecture. It can be used to find the word size of the current machine.

+ `min_integer is iso `

    Read-only flag telling the minimum integer in the
implementation. Depends on machine and Operating System architecture,
and on whether YAP uses the `GMP` multi-precision library. If
bounded is false, requests for min_integer will fail.

+ `min_tagged_integer  `

    Read-only flag telling the minimum integer we can store as a single
word. Depends on machine and Operating System
architecture.

+ `n_of_integer_keys_in_bb `

    Read or set the size of the hash table that is used for looking up the
blackboard when the key is an integer.

+ `occurs_check `

    Current read-only and set to `false`.

+ `n_of_integer_keys_in_db `

    Read or set the size of the hash table that is used for looking up the
internal data-base when the key is an integer.

+ `open_expands_filename `

    If `true` the open/3 builtin performs filename-expansion
before opening a file (SICStus Prolog like). If `false` it does not
(SWI-Prolog like).

+ `open_shared_object `

    If true, `open_shared_object/2` and friends are implemented,
providing access to shared libraries (`.so` files) or to dynamic link
libraries (`.DLL` files).

+ `profiling `

    If `off` (default) do not compile profiling information for
procedures. If `on` compile predicates so that they will output
profiling information. Profiling data can be read through the
profile_data/3 built-in.

+ `prompt_alternatives_on(atom, changeable) `

    SWI-Compatible option, determines prompting for alternatives in the Prolog toplevel. Default is <tt>groundness</tt>, YAP prompts for alternatives if and only if the query contains variables. The alternative, default in SWI-Prolog is <tt>determinism</tt> which implies the system prompts for alternatives if the goal succeeded while leaving choicepoints.

+ `redefine_warnings `

    If  _Value_ is unbound, tell whether warnings for procedures defined
in several different files are `on` or
`off`. If  _Value_ is bound to `on` enable these warnings,
and if it is bound to `off` disable them. The default for YAP is
`off`, unless we are in `sicstus` or `iso` mode.

+ `shared_object_search_path `

    Name of the environment variable used by the system to search for shared
objects.

+ `shared_object_extension `

    Suffix associated with loadable code.

+ `single_var_warnings `

    If  _Value_ is unbound, tell whether warnings for singleton variables
are `on` or `off`. If  _Value_ is bound to `on` enable
these warnings, and if it is bound to `off` disable them. The
default for YAP is `off`, unless we are in `sicstus` or
`iso` mode.

+ `strict_iso `

    If  _Value_ is unbound, tell whether strict ISO compatibility mode
is `on` or `off`. If  _Value_ is bound to `on` set
language mode to `iso` and enable strict mode. If  _Value_ is
bound to `off` disable strict mode, and keep the current language
mode. The default for YAP is `off`.
Under strict ISO Prolog mode all calls to non-ISO built-ins generate an
error. Compilation of clauses that would call non-ISO built-ins will
also generate errors. Pre-processing for grammar rules is also
disabled. Module expansion is still performed.
Arguably, ISO Prolog does not provide all the functionality required
from a modern Prolog system. Moreover, because most Prolog
implementations do not fully implement the standard and because the
standard itself gives the implementor latitude in a few important
questions, such as the unification algorithm and maximum size for
numbers there is no guarantee that programs compliant with this mode
will work the same way in every Prolog and in every platform. We thus
believe this mode is mostly useful when investigating how a program
depends on a Prolog's platform specific features.

+ `stack_dump_on_error `

    If `on` show a stack dump when YAP finds an error. The default is
`off`.

+ `syntax_errors`

    Control action to be taken after syntax errors while executing read/1,
`read/2`, or `read_term/3`:
  + `dec10`
Report the syntax error and retry reading the term.
  + `fail`
Report the syntax error and fail (default).
  + `error`
Report the syntax error and generate an error.
  + `quiet`
Just fail

+ `system_options `

    This read only flag tells which options were used to compile
YAP. Currently it informs whether the system supports `big_numbers`,
`coroutining`, `depth_limit`, `low_level_tracer`,
`or-parallelism`, `rational_trees`, `readline`, `tabling`,
`threads`, or the `wam_profiler`.

+ `tabling_mode`

    Sets or reads the tabling mode for all tabled predicates. Please
 (see Tabling) for the list of options.

+ `to_chars_mode `

    Define whether YAP should follow `quintus`-like
semantics for the `atom_chars/1` or `number_chars/1` built-in,
or whether it should follow the ISO standard (`iso` option).

+ `toplevel_hook `

    If bound, set the argument to a goal to be executed before entering the
top-level. If unbound show the current goal or `true` if none is
presented. Only the first solution is considered and the goal is not
backtracked into.

+ `toplevel_print_options `

    If bound, set the argument to the `write_term/3` options used to write
terms from the top-level. If unbound, show the current options.

+ `typein_module `

    If bound, set the current working or type-in module to the argument,
which must be an atom. If unbound, unify the argument with the current
working module.

+ `unix`

    Read-only Boolean flag that unifies with `true` if YAP is
running on an Unix system.  Defined if the C-compiler used to compile
this version of YAP either defines `__unix__` or `unix`.

+ `unknown is iso`

    Corresponds to calling the unknown/2 built-in. Possible values 
are `error`, `fail`, and `warning`.

+ `update_semantics `

    Define whether YAP should follow `immediate` update
semantics, as in C-Prolog (default), `logical` update semantics,
as in Quintus Prolog, SICStus Prolog, or in the ISO standard. There is
also an intermediate mode, `logical_assert`, where dynamic
procedures follow logical semantics but the internal data base still
follows immediate semantics.

+ `user_error `

    If the second argument is bound to a stream, set user_error to
this stream. If the second argument is unbound, unify the argument with
the current user_error stream.
By default, the user_error stream is set to a stream
corresponding to the Unix `stderr` stream.
The next example shows how to use this flag:

~~~{.prolog}
    ?- open( '/dev/null', append, Error,
            [alias(mauri_tripa)] ).

    Error = '$stream'(3) ? ;

    no
    ?- set_prolog_flag(user_error, mauri_tripa).

    close(mauri_tripa).

     yes
    ?- 
~~~
    We execute three commands. First, we open a stream in write mode and
give it an alias, in this case `mauri_tripa`. Next, we set
user_error to the stream via the alias. Note that after we did so
prompts from the system were redirected to the stream
`mauri_tripa`. Last, we close the stream. At this point, YAP
automatically redirects the user_error alias to the original
`stderr`.

+ `user_flags `

    Define the behaviour of set_prolog_flag/2 if the flag is not known. Values are `silent`, `warning` and `error`. The first two create the flag on-the-fly, with `warning` printing a message. The value `error` is consistent with ISO: it raises an existence error and does not create the flag. See also `create_prolog_flag/3`. The default is`error`, and developers are encouraged to use `create_prolog_flag/3` to create flags for their library.

+ `user_input `

    If the second argument is bound to a stream, set user_input to
this stream. If the second argument is unbound, unify the argument with
the current user_input stream.
By default, the user_input stream is set to a stream
corresponding to the Unix `stdin` stream.

+ `user_output `

    If the second argument is bound to a stream, set user_output to
this stream. If the second argument is unbound, unify the argument with
the current user_output stream.
By default, the user_output stream is set to a stream
corresponding to the Unix `stdout` stream.

+ `verbose `

    If `normal` allow printing of informational and banner messages,
such as the ones that are printed when consulting. If `silent`
disable printing these messages. It is `normal` by default except if
YAP is booted with the `-q` or `-L` flag.

+ `verbose_load `

    If `true` allow printing of informational messages when
consulting files. If `false` disable printing these messages. It
is `normal` by default except if YAP is booted with the `-L`
flag.

+ `version `

    Read-only flag that returns an atom with the current version of
YAP.

+ `version_data `

    Read-only flag that reads a term of the form
`yap`( _Major_, _Minor_, _Patch_, _Undefined_), where
 _Major_ is the major version,  _Minor_ is the minor version,
and  _Patch_ is the patch number.

+ `windows `

    Read-only boolean flag that unifies with tr `true` if YAP is
running on an Windows machine.

+ `write_strings `

    Writable flag telling whether the system should write lists of
integers that are writable character codes using the list notation. It
is `on` if enables or `off` if disabled. The default value for
this flag is `off`.

+ `max_workers `

    Read-only flag telling the maximum number of parallel processes.

+ `max_threads `

    Read-only flag telling the maximum number of Prolog threads that can 
be created.


 
*/
EOF
sed -e "585r tmp" /Users/vsc/git/yap-6.3/pl/flags.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/flags.yap

#true
cat << "EOF" > tmp
/** @pred  phrase(+ _P_, _L_, _R_) 


This predicate succeeds when the difference list ` _L_- _R_`
is a phrase of type  _P_.

 
*/
EOF
sed -e "63r tmp" /Users/vsc/git/yap-6.3/pl/grammar.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/grammar.yap

#true
cat << "EOF" > tmp
/** @pred  phrase(+ _P_, _L_)

This predicate succeeds when  _L_ is a phrase of type  _P_. The
same as `phrase(P,L,[])`.

Both this predicate and the previous are used as a convenient way to
start execution of grammar rules.

 
*/
EOF
sed -e "63r tmp" /Users/vsc/git/yap-6.3/pl/grammar.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/grammar.yap

#false
cat << "EOF" > tmp
/** @pred  exception(+ _Exception_, + _Context_, - _Action_) 


Dynamic predicate, normally not defined. Called by the Prolog system on run-time exceptions that can be repaired `just-in-time`. The values for  _Exception_ are described below. See also catch/3 and throw/1.
If this hook predicate succeeds it must instantiate the  _Action_ argument to the atom `fail` to make the operation fail silently, `retry` to tell Prolog to retry the operation or `error` to make the system generate an exception. The action `retry` only makes sense if this hook modified the environment such that the operation can now succeed without error.

+ `undefined_predicate`
 _Context_ is instantiated to a predicate-indicator ( _Module:Name/Arity_). If the predicate fails Prolog will generate an existence_error exception. The hook is intended to implement alternatives to the SWI built-in autoloader, such as autoloading code from a database. Do not use this hook to suppress existence errors on predicates. See also `unknown`.
+ `undefined_global_variable`
 _Context_ is instantiated to the name of the missing global variable. The hook must call nb_setval/2 or b_setval/2 before returning with the action retry.





 */
EOF
sed -e "334r tmp" /Users/vsc/git/yap-6.3/pl/init.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/init.yap

#false
cat << "EOF" > tmp
/** @pred  user:message_hook(+ _Term_, + _Kind_, + _Lines_) 


Hook predicate that may be define in the module `user` to intercept
messages from print_message/2.  _Term_ and  _Kind_ are the
same as passed to print_message/2.  _Lines_ is a list of
format statements as described with print_message_lines/3.

This predicate should be defined dynamic and multifile to allow other
modules defining clauses for it too.

 
*/
EOF
sed -e "308r tmp" /Users/vsc/git/yap-6.3/pl/init.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/init.yap

#false
cat << "EOF" > tmp
/** @pred  false is iso 


The same as fail.

 
*/
EOF
sed -e "68r tmp" /Users/vsc/git/yap-6.3/pl/init.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/init.yap

#false
cat << "EOF" > tmp
/** @pred  fail is iso 


Always fails.

 
*/
EOF
sed -e "59r tmp" /Users/vsc/git/yap-6.3/pl/init.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/init.yap

#true
cat << "EOF" > tmp
/** @pred  portray_clause(+ _C_) 


Write clause  _C_ as if written by listing/0.

 
*/
EOF
sed -e "218r tmp" /Users/vsc/git/yap-6.3/pl/listing.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/listing.yap

#true
cat << "EOF" > tmp
/** @pred  portray_clause(+ _S_,+ _C_)

Write clause  _C_ on stream  _S_ as if written by listing/0.

 
*/
EOF
sed -e "207r tmp" /Users/vsc/git/yap-6.3/pl/listing.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/listing.yap

#true
cat << "EOF" > tmp
/** @pred  listing(+ _P_)

Lists predicate  _P_ if its source code is available.

 
*/
EOF
sed -e "78r tmp" /Users/vsc/git/yap-6.3/pl/listing.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/listing.yap

#true
cat << "EOF" > tmp
/** @pred  listing 


Lists in the current output stream all the clauses for which source code
is available (these include all clauses for dynamic predicates and
clauses for static predicates compiled when source mode was `on`).

 
*/
EOF
sed -e "58r tmp" /Users/vsc/git/yap-6.3/pl/listing.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/listing.yap

#true
cat << "EOF" > tmp
/** @pred delete(+ _List_, ? _Element_, ? _Residue_) 


True when  _List_ is a list, in which  _Element_ may or may not
occur, and  _Residue_ is a copy of  _List_ with all elements
identical to  _Element_ deleted.

 
*/
EOF
sed -e "69r tmp" /Users/vsc/git/yap-6.3/pl/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/lists.yap

#true
cat << "EOF" > tmp
/**  @pred append(? _List1_,? _List2_,? _List3_) 


Succeeds when  _List3_ unifies with the concatenation of  _List1_
and  _List2_. The predicate can be used with any instantiation
pattern (even three variables).

 
*/
EOF
sed -e "49r tmp" /Users/vsc/git/yap-6.3/pl/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/lists.yap

#true
cat << "EOF" > tmp
/** @pred member(? _Element_, ? _Set_) 


True when  _Set_ is a list, and  _Element_ occurs in it.  It may be used
to test for an element or to enumerate all the elements by backtracking.

 
*/
EOF
sed -e "36r tmp" /Users/vsc/git/yap-6.3/pl/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/lists.yap

#true
cat << "EOF" > tmp
/** @pred memberchk(+ _Element_, + _Set_) 


As member/2, but may only be used to test whether a known
 _Element_ occurs in a known Set.  In return for this limited use, it
is more efficient when it is applicable.

 
*/
EOF
sed -e "19r tmp" /Users/vsc/git/yap-6.3/pl/lists.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/lists.yap

#false
cat << "EOF" > tmp
/** @pred open_shared_object(+ _File_, - _Handle_, + _Options_)

As `open_shared_object/2`, but allows for additional flags to
be passed.  _Options_ is a list of atoms. `now` implies the
symbols are 
resolved immediately rather than lazily (default). `global` implies
symbols of the loaded object are visible while loading other shared
objects (by default they are local). Note that these flags may not
be supported by your operating system. Check the documentation of
`dlopen()` or equivalent on your operating system. Unsupported
flags  are silently ignored. 

 
*/
EOF
sed -e "170r tmp" /Users/vsc/git/yap-6.3/pl/load_foreign.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/load_foreign.yap

#false
cat << "EOF" > tmp
/** @pred open_shared_object(+ _File_, - _Handle_)

File is the name of a shared object file (called dynamic load
library in MS-Windows). This file is attached to the current process
and  _Handle_ is unified with a handle to the library. Equivalent to
`open_shared_object(File, [], Handle)`. See also
load_foreign_library/1 and `load_foreign_library/2`.

On errors, an exception `shared_object`( _Action_,
 _Message_) is raised.  _Message_ is the return value from
dlerror().

 
*/
EOF
sed -e "153r tmp" /Users/vsc/git/yap-6.3/pl/load_foreign.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/load_foreign.yap

#false
cat << "EOF" > tmp
/** @pred load_foreign_files( _Files_, _Libs_, _InitRoutine_)

should be used, from inside YAP, to load object files produced by the C
compiler. The argument  _ObjectFiles_ should be a list of atoms
specifying the object files to load,  _Libs_ is a list (possibly
empty) of libraries to be passed to the unix loader (`ld`) and
InitRoutine is the name of the C routine (to be called after the files
are loaded) to perform the necessary declarations to YAP of the
predicates defined in the files. 

YAP will search for  _ObjectFiles_ in the current directory first. If
it cannot find them it will search for the files using the environment
variable:

+ YAPLIBDIR

if defined, or in the default library.

YAP also supports the SWI-Prolog interface to loading foreign code:

 
*/
EOF
sed -e "53r tmp" /Users/vsc/git/yap-6.3/pl/load_foreign.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/load_foreign.yap

#false
cat << "EOF" > tmp
/** @pred  print_message_lines(+ _Stream_, + _Prefix_, + _Lines_) 


Print a message (see print_message/2) that has been translated to
a list of message elements.  The elements of this list are:

+ _Format_-_Args_
Where  _Format_ is an atom and  _Args_ is a list
of format argument.  Handed to `format/3`.
+ `flush`
If this appears as the last element,  _Stream_ is flushed
(see `flush_output/1`) and no final newline is generated.
+ `at_same_line`
If this appears as first element, no prefix is printed for
the first line and the line-position is not forced to 0
(see `format/1`, `~N`).
+ `<Format>`
Handed to `format/3` as `format(Stream, Format, [])`.
+ nl
A new line is started and if the message is not complete
the  _Prefix_ is printed too.


 
*/
EOF
sed -e "580r tmp" /Users/vsc/git/yap-6.3/pl/messages.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/messages.yap

#false
cat << "EOF" > tmp
/** @pred with_mutex(+ _MutexId_, : _Goal_) 


Execute  _Goal_ while holding  _MutexId_.  If  _Goal_ leaves
choicepoints, these are destroyed (as in once/1).  The mutex is unlocked
regardless of whether  _Goal_ succeeds, fails or raises an exception.
An exception thrown by  _Goal_ is re-thrown after the mutex has been
successfully unlocked.  See also `mutex_create/2`.

Although described in the thread-section, this predicate is also
available in the single-threaded version, where it behaves simply as
once/1.

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred call_shared_object_function(+ _Handle_, + _Function_) 


Call the named function in the loaded shared library. The function
is called without arguments and the return-value is
ignored. In SWI-Prolog, normally this function installs foreign
language predicates using calls to `PL_register_foreign()`.



 */
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  with_output_to(+ _Ouput_,: _Goal_) 


Run  _Goal_ as once/1, while characters written to the current
output are sent to  _Output_. The predicate is SWI-Prolog
specific.

Applications should generally avoid creating atoms by breaking and
concatenating other atoms as the creation of large numbers of
intermediate atoms generally leads to poor performance, even more so in
multi-threaded applications. This predicate supports creating
difference-lists from character data efficiently. The example below
defines the DCG rule `term/3` to insert a term in the output:

~~~~~
 term(Term, In, Tail) :-
        with_output_to(codes(In, Tail), write(Term)).

?- phrase(term(hello), X).

X = [104, 101, 108, 108, 111]
~~~~~

+ A Stream handle or alias
Temporary switch current output to the given stream. Redirection using with_output_to/2 guarantees the original output is restored, also if Goal fails or raises an exception. See also call_cleanup/2. 
+ atom(- _Atom_)
Create an atom from the emitted characters. Please note the remark above. 
+ string(- _String_)
Create a string-object (not supported in YAP). 
+ codes(- _Codes_)
Create a list of character codes from the emitted characters, similar to atom_codes/2. 
+ codes(- _Codes_, - _Tail_)
Create a list of character codes as a difference-list. 
+ chars(- _Chars_)
Create a list of one-character-atoms codes from the emitted characters, similar to atom_chars/2. 
+ chars(- _Chars_, - _Tail_)
Create a list of one-character-atoms as a difference-list. 





 */
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  setof( _X_,+ _P_,- _B_) is iso 


Similar to `bagof( _T_, _G_, _L_)` but sorts list
 _L_ and keeping only one copy of each element.  Again, assuming the
same clauses as in the examples above, the reply to the query

~~~~~
setof(X,a(X,Y),L).
~~~~~
would be:

~~~~~
X = _32
Y = 1
L = [1,2];
X = _32
Y = 2
L = [2];
no
~~~~~




 */
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  format(+ _T_,+ _L_) 


Print formatted output to the current output stream. The arguments in
list  _L_ are output according to the string or atom  _T_.

A control sequence is introduced by a `w`. The following control
sequences are available in YAP:



+ `~~`
Print a single tilde.

+ `~a`
The next argument must be an atom, that will be printed as if by `write`.

+ `~Nc`
The next argument must be an integer, that will be printed as a
character code. The number  _N_ is the number of times to print the
character (default 1).

+ `~Ne`
+ `~NE`
+ `~Nf`
+ `~Ng`
+ `~NG`
The next argument must be a floating point number. The float  _F_, the number
 _N_ and the control code `c` will be passed to `printf` as:

~~~~~{.prolog}
    printf("%s.Nc", F)
~~~~~

As an example:

~~~~~{.prolog}
?- format("~8e, ~8E, ~8f, ~8g, ~8G~w",
          [3.14,3.14,3.14,3.14,3.14,3.14]).
3.140000e+00, 3.140000E+00, 3.140000, 3.14, 3.143.14
~~~~~

+ `~Nd`
The next argument must be an integer, and  _N_ is the number of digits
after the decimal point. If  _N_ is `0` no decimal points will be
printed. The default is  _N = 0_.

~~~~~{.prolog}
?- format("~2d, ~d",[15000, 15000]).
150.00, 15000
~~~~~

+ `~ND`
Identical to `~Nd`, except that commas are used to separate groups
of three digits.

~~~~~{.prolog}
?- format("~2D, ~D",[150000, 150000]).
1,500.00, 150,000
~~~~~

+ `~i`
Ignore the next argument in the list of arguments:

~~~~~{.prolog}
?- format('The ~i met the boregrove',[mimsy]).
The  met the boregrove
~~~~~

+ `~k`
Print the next argument with `write_canonical`:

~~~~~{.prolog}
?- format("Good night ~k",a+[1,2]).
Good night +(a,[1,2])
~~~~~

+ `~Nn`
Print  _N_ newlines (where  _N_ defaults to 1).

+ `~NN`
Print  _N_ newlines if at the beginning of the line (where  _N_
defaults to 1).

+ `~Nr`
The next argument must be an integer, and  _N_ is interpreted as a
radix, such that `2 <= N <= 36` (the default is 8).

~~~~~{.prolog}
?- format("~2r, 0x~16r, ~r",
          [150000, 150000, 150000]).
100100100111110000, 0x249f0, 444760
~~~~~

Note that the letters `a-z` denote digits larger than 9.

+ `~NR`
Similar to `~NR`. The next argument must be an integer, and  _N_ is
interpreted as a radix, such that `2 <= N <= 36` (the default is 8).

~~~~~{.prolog}
?- format("~2r, 0x~16r, ~r",
          [150000, 150000, 150000]).
100100100111110000, 0x249F0, 444760
~~~~~

The only difference is that letters `A-Z` denote digits larger than 9.

+ `~p`
Print the next argument with print/1:

~~~~~{.prolog}
?- format("Good night ~p",a+[1,2]).
Good night a+[1,2]
~~~~~

+ `~q`
Print the next argument with writeq/1:

~~~~~{.prolog}
?- format("Good night ~q",'Hello'+[1,2]).
Good night 'Hello'+[1,2]
~~~~~

+ `~Ns`
The next argument must be a list of character codes. The system then
outputs their representation as a string, where  _N_ is the maximum
number of characters for the string ( _N_ defaults to the length of the
string).

~~~~~{.prolog}
?- format("The ~s are ~4s",["woods","lovely"]).
The woods are love
~~~~~

+ `~w`
Print the next argument with write/1:

~~~~~
?- format("Good night ~w",'Hello'+[1,2]).
Good night Hello+[1,2]
~~~~~


The number of arguments, `N`, may be given as an integer, or it
may be given as an extra argument. The next example shows a small
procedure to write a variable number of `a` characters:

~~~~~
write_many_as(N) :-
        format("~*c",[N,0'a]).
~~~~~

The format/2 built-in also allows for formatted output.  One can
specify column boundaries and fill the intermediate space by a padding
character: 

+ `~N|`
Set a column boundary at position  _N_, where  _N_ defaults to the
current position.

+ `~N+`
Set a column boundary at  _N_ characters past the current position, where
 _N_ defaults to `8`.

+ `~Nt`
Set padding for a column, where  _N_ is the fill code (default is
`SPC`).



The next example shows how to align columns and padding. We first show
left-alignment:

~~~~~
   ?- format("~n*Hello~16+*~n",[]).
*Hello          *
~~~~~

Note that we reserve 16 characters for the column.

The following example shows how to do right-alignment:

~~~~~
   ?- format("*~tHello~16+*~n",[]).
*          Hello*

~~~~~

The `~t` escape sequence forces filling before `Hello`. 

We next show how to do centering:

~~~~~
   ?- format("*~tHello~t~16+*~n",[]).
*     Hello     *
~~~~~

The two `~t` escape sequence force filling both before and after
`Hello`. Space is then evenly divided between the right and the
left sides.

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  format(+ _S_,+ _T_,+ _L_)

Print formatted output to stream  _S_.

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  findall( _T_,+ _G_,- _L_) is iso 


Unifies  _L_ with a list that contains all the instantiations of the
term  _T_ satisfying the goal  _G_.

With the following program:

~~~~~
a(2,1).
a(1,1).
a(2,2).
~~~~~
the answer to the query

~~~~~
findall(X,a(X,Y),L).
~~~~~
would be:

~~~~~
X = _32
Y = _33
L = [2,1,2];
no
~~~~~

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  findall( _T_,+ _G_,+ _L_,- _L0_)

Similar to findall/3, but appends all answers to list  _L0_.

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  call_with_args(+ _Name_,...,? _Ai_,...) 


Meta-call where  _Name_ is the name of the procedure to be called and
the  _Ai_ are the arguments. The number of arguments varies between 0
and 10. New code should use `call/N` for better portability.

If  _Name_ is a complex term, then call_with_args/n behaves as
call/n:

~~~~~{.prolog}
call(p(X1,...,Xm), Y1,...,Yn) :- p(X1,...,Xm,Y1,...,Yn).
~~~~~

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  bb_update(+ _Key_,? _Term_,? _New_) 


Atomically  unify a term stored in the blackboard under key  _Key_
with  _Term_, and if the unification succeeds replace it by
 _New_. Fail silently if no such term exists or if unification fails.




 */
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  bb_put(+ _Key_,? _Term_) 


Store term table  _Term_ in the blackboard under key  _Key_. If a
previous term was stored under key  _Key_ it is simply forgotten.

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  bb_get(+ _Key_,? _Term_) 


Unify  _Term_ with a term stored in the blackboard under key
 _Key_, or fail silently if no such term exists.

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  bb_delete(+ _Key_,? _Term_) 


Delete any term stored in the blackboard under key  _Key_ and unify
it with  _Term_. Fail silently if no such term exists.

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  bagof( _T_,+ _G_,- _L_) is iso 


For each set of possible instances of the free variables occurring in
 _G_ but not in  _T_, generates the list  _L_ of the instances of
 _T_ satisfying  _G_. Again, assuming the same clauses as in the
examples above, the reply to the query

~~~~~
bagof(X,a(X,Y),L).

would be:
X = _32
Y = 1
L = [2,1];
X = _32
Y = 2
L = [2];
no
~~~~~

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  all( _T_,+ _G_,- _L_) 


Similar to `findall( _T_, _G_, _L_)` but eliminate
repeated elements. Thus, assuming the same clauses as in the above
example, the reply to the query

~~~~~
all(X,a(X,Y),L).
~~~~~
would be:

~~~~~
X = _32
Y = _33
L = [2,1];
no
~~~~~

Note that all/3 will fail if no answers are found.

 
*/
EOF
sed -e "1060r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  current_module( _M_, _F_)

Succeeds if  _M_ are current modules associated to the file  _F_.




 */
EOF
sed -e "553r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred  current_module( _M_) 


Succeeds if  _M_ are defined modules. A module is defined as soon as some
predicate defined in the module is loaded, as soon as a goal in the
module is called, or as soon as it becomes the current type-in module.

 
*/
EOF
sed -e "537r tmp" /Users/vsc/git/yap-6.3/pl/modules.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/modules.yap

#false
cat << "EOF" > tmp
/** @pred setenv(+ _Name_,+ _Value_) 


Set environment variable.   _Name_ and  _Value_ should be
instantiated to atoms or integers.  The environment variable will be
passed to `shell/[0-2]` and can be requested using `getenv/2`.
They also influence expand_file_name/2.

 
*/
EOF
sed -e "215r tmp" /Users/vsc/git/yap-6.3/pl/os.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/os.yap

#false
cat << "EOF" > tmp
/** @pred  putenv(+ _E_,+ _S_) 


Set environment variable  _E_ to the value  _S_. If the
environment variable  _E_ does not exist, create a new one. Both the
environment variable and the value must be atoms.

 
*/
EOF
sed -e "199r tmp" /Users/vsc/git/yap-6.3/pl/os.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/os.yap

#false
cat << "EOF" > tmp
/** @pred  unix(+ _S_) 


Access to Unix-like functionality:

+ argv/1
Return a list of arguments to the program. These are the arguments that
follow a `--`, as in the usual Unix convention.
+ cd/0
Change to home directory.
+ cd/1
Change to given directory. Acceptable directory names are strings or
atoms.
+ environ/2
If the first argument is an atom, unify the second argument with the
value of the corresponding environment variable.
+ getcwd/1
Unify the first argument with an atom representing the current directory.
+ putenv/2
Set environment variable  _E_ to the value  _S_. If the
environment variable  _E_ does not exist, create a new one. Both the
environment variable and the value must be atoms.
+ shell/1
Execute command under current shell. Acceptable commands are strings or
atoms.
+ system/1
Execute command with `/bin/sh`. Acceptable commands are strings or
atoms.
+ shell/0
Execute a new shell.


 
*/
EOF
sed -e "140r tmp" /Users/vsc/git/yap-6.3/pl/os.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/os.yap

#false
cat << "EOF" > tmp
/** @pred  pwd 


Prints the current directory.

 
*/
EOF
sed -e "102r tmp" /Users/vsc/git/yap-6.3/pl/os.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/os.yap

#false
cat << "EOF" > tmp
/** @pred  ls 


Prints a list of all files in the current directory.

 
*/
EOF
sed -e "70r tmp" /Users/vsc/git/yap-6.3/pl/os.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/os.yap

#false
cat << "EOF" > tmp
/** @pred  getcwd(- _D_) 


Unify the current directory, represented as an atom, with the argument
 _D_.

 
*/
EOF
sed -e "61r tmp" /Users/vsc/git/yap-6.3/pl/os.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/os.yap

#false
cat << "EOF" > tmp
/** @pred  cd(+ _D_) 


Changes the current directory (on UNIX environments).

 
*/
EOF
sed -e "49r tmp" /Users/vsc/git/yap-6.3/pl/os.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/os.yap

#false
cat << "EOF" > tmp
/** @pred  cd

Changes the current directory (on UNIX environments) to the user's home directory.

 
*/
EOF
sed -e "39r tmp" /Users/vsc/git/yap-6.3/pl/os.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/os.yap

#false
cat << "EOF" > tmp
/** @pred  dynamic( + _P_ )


Declares predicate  _P_ or list of predicates [ _P1_,..., _Pn_]
as a dynamic predicate.  _P_ must be written as a predicate indicator, that is in form
 _Name/Arity_ or _Module:Name/Arity_.

~~~~~
:- dynamic god/1.
~~~~~

 
a more convenient form can be used:

~~~~~
:- dynamic son/3, father/2, mother/2.
~~~~~

or, equivalently,

~~~~~
:- dynamic [son/3, father/2, mother/2].
~~~~~

Note:

a predicate is assumed to be dynamic when 
asserted before being defined.

 
*/
EOF
sed -e "72r tmp" /Users/vsc/git/yap-6.3/pl/preddecls.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preddecls.yap

#false
cat << "EOF" > tmp
/** @pred  compile_predicates(: _ListOfNameArity_) 



Compile a list of specified dynamic predicates (see dynamic/1 and
assert/1 into normal static predicates. This call tells the
Prolog environment the definition will not change anymore and further
calls to assert/1 or retract/1 on the named predicates
raise a permission error. This predicate is designed to deal with parts
of the program that is generated at runtime but does not change during
the remainder of the program execution.




 */
EOF
sed -e "1257r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  current_key(? _A_,? _K_) 


Defines the relation:  _K_ is a currently defined database key whose
name is the atom  _A_. It can be used to generate all the keys for
the internal data-base.

 
*/
EOF
sed -e "1231r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  current_predicate( _F_) is iso 


 _F_ is the predicate indicator for a currently defined user or
library predicate.  _F_ is of the form  _Na/Ar_, where the atom
 _Na_ is the name of the predicate, and  _Ar_ its arity.

 
*/
EOF
sed -e "1208r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  system_predicate( _A_, _P_) 


Defines the relation:   _P_ is a built-in predicate whose name
is the atom  _A_.

 
*/
EOF
sed -e "1182r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  current_predicate( _A_, _P_)

Defines the relation:  _P_ is a currently defined predicate whose
name is the atom  _A_.

 
*/
EOF
sed -e "1168r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  predicate_erased_statistics( _P_, _NCls_, _Sz_, _IndexSz_)  


Given predicate  _P_,  _NCls_ is the number of erased clauses for
 _P_ that could not be discarded yet,  _Sz_ is the amount of space
taken to store those clauses (in bytes), and  _IndexSz_ is the amount
of space required to store indices to those clauses (in bytes).




 */
EOF
sed -e "1154r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  predicate_statistics( _P_, _NCls_, _Sz_, _IndexSz_)  


Given predicate  _P_,  _NCls_ is the number of clauses for
 _P_,  _Sz_ is the amount of space taken to store those clauses
(in bytes), and  _IndexSz_ is the amount of space required to store
indices to those clauses (in bytes).

 
*/
EOF
sed -e "1122r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  predicate_property( _P_, _Prop_) is iso 


For the predicates obeying the specification  _P_ unify  _Prop_
with a property of  _P_. These properties may be:

+ `built_in `
true for built-in predicates,

+ `dynamic`
true if the predicate is dynamic

+ `static `
true if the predicate is static

+ `meta_predicate( _M_) `
true if the predicate has a meta_predicate declaration  _M_.

+ `multifile `
true if the predicate was declared to be multifile

+ `imported_from( _Mod_) `
true if the predicate was imported from module  _Mod_.

+ `exported `
true if the predicate is exported in the current module.

+ `public`
true if the predicate is public; note that all dynamic predicates are
public.

+ `tabled `
true if the predicate is tabled; note that only static predicates can
be tabled in YAP.

+ `source (predicate_property flag) `
true if source for the predicate is available.

+ `number_of_clauses( _ClauseCount_) `
Number of clauses in the predicate definition. Always one if external
or built-in.


 
*/
EOF
sed -e "1046r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  dynamic_predicate(+ _P_,+ _Semantics_) 


Declares predicate  _P_ or list of predicates [ _P1_,..., _Pn_]
as a dynamic predicate following either `logical` or
`immediate` semantics.

 
*/
EOF
sed -e "924r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  abolish(+ _PredSpec_) is iso 


Deletes the predicate given by  _PredSpec_ from the database. If
 _PredSpec_ is an unbound variable, delete all predicates for the
current module. The
specification must include the name and arity, and it may include module
information. Under <tt>iso</tt> language mode this built-in will only abolish
dynamic procedures. Under other modes it will abolish any procedures. 

 
*/
EOF
sed -e "750r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  abolish(+ _P_,+ _N_)

Deletes the predicate with name  _P_ and arity  _N_. It will remove
both static and dynamic predicates.

 
*/
EOF
sed -e "721r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  retractall(+ _G_) is iso 


Retract all the clauses whose head matches the goal  _G_. Goal
 _G_ must be a call to a dynamic predicate.




 */
EOF
sed -e "659r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  retract(+ _C_,- _R_)

Erases from the program the clause  _C_ whose 
database reference is  _R_. The predicate must be dynamic.




 */
EOF
sed -e "621r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  retract(+ _C_) is iso 


Erases the first clause in the program that matches  _C_. This
predicate may also be used for the static predicates that have been
compiled when the source mode was `on`. For more information on
source/0 ( (see Setting the Compiler)).

 
*/
EOF
sed -e "575r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  nth_clause(+ _H_, _I_,- _R_) 


Find the  _I_th clause in the predicate defining  _H_, and give
a reference to the clause. Alternatively, if the reference  _R_ is
given the head  _H_ is unified with a description of the predicate
and  _I_ is bound to its position.



The following predicates can only be used for dynamic predicates:



 
*/
EOF
sed -e "552r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  clause(+ _H_, _B_,- _R_)

The same as clause/2, plus  _R_ is unified with the
reference to the clause in the database. You can use instance/2
to access the reference's value. Note that you may not use
erase/1 on the reference on static procedures.

 
*/
EOF
sed -e "471r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  clause(+ _H_, _B_) is iso 


A clause whose head matches  _H_ is searched for in the
program. Its head and body are respectively unified with  _H_ and
 _B_. If the clause is a unit clause,  _B_ is unified with
 _true_.

This predicate is applicable to static procedures compiled with
`source` active, and to all dynamic procedures.

 
*/
EOF
sed -e "456r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  assert(+ _C_,- _R_)

The same as `assert(C)` ( (see Modifying the Database)) but
unifies  _R_ with the  database reference that identifies the new
clause, in a one-to-one way. Note that `asserta/2` only works for dynamic
predicates. If the predicate is undefined, it will automatically be
declared dynamic.

 
*/
EOF
sed -e "437r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  assertz(+ _C_,- _R_)

The same as `assertz(C)` but unifying  _R_ with
the  database reference that identifies the new clause, in a 
one-to-one way. Note that `asserta/2` only works for dynamic
predicates. If the predicate is undefined, it will automatically be
declared dynamic.

 
*/
EOF
sed -e "421r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  asserta(+ _C_,- _R_)

The same as `asserta(C)` but unifying  _R_ with
the  database reference that identifies the new clause, in a 
one-to-one way. Note that `asserta/2` only works for dynamic
predicates. If the predicate is undefined, it will automatically be
declared dynamic.

 
*/
EOF
sed -e "405r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  assertz_static(: _C_) 


Adds clause  _C_ to the end of a static procedure.  Asserting a
static clause for a predicate while choice-points for the predicate are
available has undefined results.



The following predicates can be used for dynamic predicates and for
static predicates, if source mode was on when they were compiled:



 
*/
EOF
sed -e "299r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  asserta_static(: _C_) 


Adds clause  _C_ to the beginning of a static procedure. 

 
*/
EOF
sed -e "275r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  assert_static(: _C_) 


Adds clause  _C_ to a static procedure. Asserting a static clause
for a predicate while choice-points for the predicate are available has
undefined results.

 
*/
EOF
sed -e "262r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  assert(+ _C_) 


Same as assertz/1. Adds clause  _C_ to the program. If the predicate is undefined,
declare it as dynamic. New code should use assertz/1 for better portability.

Most Prolog systems only allow asserting clauses for dynamic
predicates. This is also as specified in the ISO standard. YAP allows
asserting clauses for static predicates, as long as the predicate is not
in use and the language flag is <tt>cprolog</tt>. Note that this feature is
deprecated, if you want to assert clauses for static procedures you
should use assert_static/1.

 
*/
EOF
sed -e "154r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  assertz(+ _C_) is iso 


Adds clause  _C_ to the end of the program. If the predicate is
undefined, declare it as dynamic.

Most Prolog systems only allow asserting clauses for dynamic
predicates. This is also as specified in the ISO standard. YAP allows
asserting clauses for static predicates. The current version of YAP
supports this feature, but this feature is deprecated and support may go
away in future versions.

 
*/
EOF
sed -e "133r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  asserta(+ _C_) is iso 


Adds clause  _C_ to the beginning of the program. If the predicate is
undefined, declare it as dynamic.

 
*/
EOF
sed -e "113r tmp" /Users/vsc/git/yap-6.3/pl/preds.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/preds.yap

#false
cat << "EOF" > tmp
/** @pred  showprofres( _N_)

Show profiling info for the top-most  _N_ predicates.



The showprofres/0 and `showprofres/1` predicates call a user-defined multifile hook predicate, `user:prolog_predicate_name/2`, that can be used for converting a possibly explicitly-qualified callable term into an atom that will used when printing the profiling information.


 */
EOF
sed -e "164r tmp" /Users/vsc/git/yap-6.3/pl/profile.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/profile.yap

#false
cat << "EOF" > tmp
/** @pred  showprofres 


Show profiling info.

 
*/
EOF
sed -e "151r tmp" /Users/vsc/git/yap-6.3/pl/profile.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/profile.yap

#false
cat << "EOF" > tmp
/** @pred  profile_data(? _Na/Ar_, ? _Parameter_, - _Data_) 


Give current profile data on  _Parameter_ for a predicate described
by the predicate indicator  _Na/Ar_. If any of  _Na/Ar_ or
 _Parameter_ are unbound, backtrack through all profiled predicates
or stored parameters. Current parameters are:

+ calls
Number of times a procedure was called.

+ retries
Number of times a call to the procedure was backtracked to and retried.


+ profile_reset 


Reset all profiling information.




 */
EOF
sed -e "102r tmp" /Users/vsc/git/yap-6.3/pl/profile.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/profile.yap

#false
cat << "EOF" > tmp
/** @pred  on_signal(+ _Signal_,? _OldAction_,+ _Callable_) 


Set the interrupt handler for soft interrupt  _Signal_ to be
 _Callable_.  _OldAction_ is unified with the previous handler.

Only a subset of the software interrupts (signals) can have their
handlers manipulated through on_signal/3.
Their POSIX names, YAP names and default behavior is given below.
The "YAP name" of the signal is the atom that is associated with
each signal, and should be used as the first argument to
on_signal/3. It is chosen so that it matches the signal's POSIX
name.

on_signal/3 succeeds, unless when called with an invalid
signal name or one that is not supported on this platform. No checks
are made on the handler provided by the user.

+ sig_up (Hangup)
SIGHUP in Unix/Linux; Reconsult the initialization files
~/.yaprc, ~/.prologrc and ~/prolog.ini.
+ sig_usr1 and sig_usr2 (User signals)
SIGUSR1 and SIGUSR2 in Unix/Linux; Print a message and halt.


A special case is made, where if  _Callable_ is bound to
`default`, then the default handler is restored for that signal.

A call in the form `on_signal( _S_, _H_, _H_)` can be used
to retrieve a signal's current handler without changing it.

It must be noted that although a signal can be received at all times,
the handler is not executed while YAP is waiting for a query at the
prompt. The signal will be, however, registered and dealt with as soon
as the user makes a query.

Please also note, that neither POSIX Operating Systems nor YAP guarantee
that the order of delivery and handling is going to correspond with the
order of dispatch.




 */
EOF
sed -e "147r tmp" /Users/vsc/git/yap-6.3/pl/signals.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/signals.yap

#true
cat << "EOF" > tmp
/** @pred  alarm(+ _Seconds_,+ _Callable_,+ _OldAlarm_) 


Arranges for YAP to be interrupted in  _Seconds_ seconds, or in
[ _Seconds_| _MicroSeconds_]. When interrupted, YAP will execute
 _Callable_ and then return to the previous execution. If
 _Seconds_ is `0`, no new alarm is scheduled. In any event,
any previously set alarm is canceled.

The variable  _OldAlarm_ unifies with the number of seconds remaining
until any previously scheduled alarm was due to be delivered, or with
`0` if there was no previously scheduled alarm.

Note that execution of  _Callable_ will wait if YAP is
executing built-in predicates, such as Input/Output operations.

The next example shows how  _alarm/3_ can be used to implement a
simple clock:

~~~~~
loop :- loop.

ticker :- write('.'), flush_output,
          get_value(tick, yes),
          alarm(1,ticker,_).

:- set_value(tick, yes), alarm(1,ticker,_), loop.
~~~~~

The clock, `ticker`, writes a dot and then checks the flag
`tick` to see whether it can continue ticking. If so, it calls
itself again. Note that there is no guarantee that the each dot
corresponds a second: for instance, if the YAP is waiting for
user input, `ticker` will wait until the user types the entry in.

The next example shows how alarm/3 can be used to guarantee that
a certain procedure does not take longer than a certain amount of time:

~~~~~
loop :- loop.

:-   catch((alarm(10, throw(ball), _),loop),
        ball,
        format('Quota exhausted.~n',[])).
~~~~~
In this case after `10` seconds our `loop` is interrupted,
`ball` is thrown,  and the handler writes `Quota exhausted`.
Execution then continues from the handler.

Note that in this case `loop/0` always executes until the alarm is
sent. Often, the code you are executing succeeds or fails before the
alarm is actually delivered. In this case, you probably want to disable
the alarm when you leave the procedure. The next procedure does exactly so:

~~~~~
once_with_alarm(Time,Goal,DoOnAlarm) :-
   catch(execute_once_with_alarm(Time, Goal), alarm, DoOnAlarm).

execute_once_with_alarm(Time, Goal) :-
        alarm(Time, alarm, _),
        ( call(Goal) -> alarm(0, alarm, _) ; alarm(0, alarm, _), fail).
~~~~~

The procedure `once_with_alarm/3` has three arguments:
the  _Time_ to wait before the alarm is
sent; the  _Goal_ to execute; and the goal  _DoOnAlarm_ to execute
if the alarm is sent. It uses catch/3 to handle the case the
`alarm` is sent. Then it starts the alarm, calls the goal
 _Goal_, and disables the alarm on success or failure.

 
*/
EOF
sed -e "147r tmp" /Users/vsc/git/yap-6.3/pl/signals.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/signals.yap

#false
cat << "EOF" > tmp
/** @pred  predsort(+ _Pred_, + _List_, - _Sorted_) 


Sorts similar to sort/2, but determines the order of two terms by
calling  _Pred_(- _Delta_, + _E1_, + _E2_) . This call must
unify  _Delta_ with one of `<`, `>` or `=`. If
built-in predicate compare/3 is used, the result is the same as
sort/2.

 
*/
EOF
sed -e "172r tmp" /Users/vsc/git/yap-6.3/pl/sort.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/sort.yap

#false
cat << "EOF" > tmp
/** @pred  keysort(+ _L_, _S_) is iso 


Assuming L is a list of the form ` _Key_- _Value_`,
`keysort(+ _L_, _S_)` unifies  _S_ with the list obtained
from  _L_, by sorting its elements according to the value of
 _Key_.

~~~~~{.prolog}
?- keysort([3-a,1-b,2-c,1-a,1-b],S).
~~~~~
would return:

~~~~~{.prolog}
S = [1-b,1-a,1-b,2-c,3-a]
~~~~~

 
*/
EOF
sed -e "134r tmp" /Users/vsc/git/yap-6.3/pl/sort.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/sort.yap

#false
cat << "EOF" > tmp
/** @pred  sort(+ _L_,- _S_) is iso 


Unifies  _S_ with the list obtained by sorting  _L_ and  merging
identical (in the sense of `==`) elements.

 
*/
EOF
sed -e "88r tmp" /Users/vsc/git/yap-6.3/pl/sort.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/sort.yap

#false
cat << "EOF" > tmp
/** @pred  length(? _L_,? _S_) 


Unify the well-defined list  _L_ with its length. The procedure can
be used to find the length of a pre-defined list, or to build a list
of length  _S_.




 */
EOF
sed -e "52r tmp" /Users/vsc/git/yap-6.3/pl/sort.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/sort.yap

#true
cat << "EOF" > tmp
/** @pred  time(: _Goal_) 


Prints the CPU time and the wall time for the execution of  _Goal_.
Possible choice-points of  _Goal_ are removed. Based on the SWI-Prolog 
definition (minus reporting the number of inferences, which YAP currently
does not support).

 
*/
EOF
sed -e "328r tmp" /Users/vsc/git/yap-6.3/pl/statistics.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/statistics.yap

#true
cat << "EOF" > tmp
/** @pred  key_statistics(+ _K_,- _Entries_,- _TotalSize_)

Returns several statistics for a key  _K_. Currently, it says how
many entries we have for that key,  _Entries_, what is the
total size spent on this key.

 
*/
EOF
sed -e "307r tmp" /Users/vsc/git/yap-6.3/pl/statistics.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/statistics.yap

#true
cat << "EOF" > tmp
/** @pred  statistics(? _Param_,- _Info_)

Gives statistical information on the system parameter given by first
argument:



+ atoms 

`[ _NumberOfAtoms_, _SpaceUsedBy Atoms_]`


This gives the total number of atoms `NumberOfAtoms` and how much
space they require in bytes,  _SpaceUsedBy Atoms_.

+ cputime 

`[ _Time since Boot_, _Time From Last Call to Cputime_]`


This gives the total cputime in milliseconds spent executing Prolog code,
garbage collection and stack shifts time included.

+ dynamic_code 

`[ _Clause Size_, _Index Size_, _Tree Index Size_, _Choice Point Instructions Size_, _Expansion Nodes Size_, _Index Switch Size_]`


Size of static code in YAP in bytes:  _Clause Size_, the number of
bytes allocated for clauses, plus
 _Index Size_, the number of bytes spent in the indexing code. The
indexing code is divided into main tree,  _Tree Index Size_, 
tables that implement choice-point manipulation,  _Choice xsPoint Instructions Size_, tables that cache clauses for future expansion of the index
tree,  _Expansion Nodes Size_, and 
tables such as hash tables that select according to value,   _Index Switch Size_.

+ garbage_collection 

`[ _Number of GCs_, _Total Global Recovered_, _Total Time Spent_]`


Number of garbage collections, amount of space recovered in kbytes, and
total time spent doing garbage collection in milliseconds. More detailed
information is available using `yap_flag(gc_trace,verbose)`.

+ global_stack 

`[ _Global Stack Used_, _Execution Stack Free_]`


Space in kbytes currently used in the global stack, and space available for
expansion by the local and global stacks.

+ local_stack 

`[ _Local Stack Used_, _Execution Stack Free_]`


Space in kbytes currently used in the local stack, and space available for
expansion by the local and global stacks.

+ heap 

`[ _Heap Used_, _Heap Free_]`


Total space in kbytes not recoverable
in backtracking. It includes the program code, internal data base, and,
atom symbol table.

+ program 

`[ _Program Space Used_, _Program Space Free_]`


Equivalent to heap.

+ runtime 

`[ _Time since Boot_, _Time From Last Call to Runtime_]`


This gives the total cputime in milliseconds spent executing Prolog
code, not including garbage collections and stack shifts. Note that
until YAP4.1.2 the runtime statistics would return time spent on
garbage collection and stack shifting.

+ stack_shifts 

`[ _Number of Heap Shifts_, _Number of Stack Shifts_, _Number of Trail Shifts_]`


Number of times YAP had to
expand the heap, the stacks, or the trail. More detailed information is
available using `yap_flag(gc_trace,verbose)`.

+ static_code 

`[ _Clause Size_, _Index Size_, _Tree Index Size_, _Expansion Nodes Size_, _Index Switch Size_]`


Size of static code in YAP in bytes:  _Clause Size_, the number of
bytes allocated for clauses, plus
 _Index Size_, the number of bytes spent in the indexing code. The
indexing code is divided into a main tree,  _Tree Index Size_, table that cache clauses for future expansion of the index
tree,  _Expansion Nodes Size_, and and 
tables such as hash tables that select according to value,   _Index Switch Size_.

+ trail 

`[ _Trail Used_, _Trail Free_]`


Space in kbytes currently being used and still available for the trail.

+ walltime 

`[ _Time since Boot_, _Time From Last Call to Walltime_]`


This gives the clock time in milliseconds since starting Prolog.



 
*/
EOF
sed -e "256r tmp" /Users/vsc/git/yap-6.3/pl/statistics.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/statistics.yap

#true
cat << "EOF" > tmp
/** @pred  statistics/0 


Send to the current user error stream general information on space used and time
spent by the system.

~~~~~
?- statistics.
memory (total)        4784124 bytes
   program space      3055616 bytes:    1392224 in use,      1663392 free
                                                             2228132  max
   stack space        1531904 bytes:        464 in use,      1531440 free
     global stack:                           96 in use,       616684  max
      local stack:                          368 in use,       546208  max
   trail stack         196604 bytes:          8 in use,       196596 free

       0.010 sec. for 5 code, 2 stack, and 1 trail space overflows
       0.130 sec. for 3 garbage collections which collected 421000 bytes
       0.000 sec. for 0 atom garbage collections which collected 0 bytes
       0.880 sec. runtime
       1.020 sec. cputime
      25.055 sec. elapsed time

~~~~~
The example shows how much memory the system spends. Memory is divided
into Program Space, Stack Space and Trail. In the example we have 3MB
allocated for program spaces, with less than half being actually
used. YAP also shows the maximum amount of heap space having been used
which was over 2MB.

The stack space is divided into two stacks which grow against each
other. We are in the top level so very little stack is being used. On
the other hand, the system did use a lot of global and local stack
during the previous execution (we refer the reader to a WAM tutorial in
order to understand what are the global and local stacks).

YAP also shows information on how many memory overflows and garbage
collections the system executed, and statistics on total execution
time. Cputime includes all running time, runtime excludes garbage
collection and stack overflow time.

 
*/
EOF
sed -e "68r tmp" /Users/vsc/git/yap-6.3/pl/statistics.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/statistics.yap

#true
cat << "EOF" > tmp
/** @pred reverse(+ _List_, ? _Reversed_) 


True when  _List_ and  _Reversed_ are lists with the same elements
but in opposite orders. 

 
*/
EOF
sed -e "81r tmp" /Users/vsc/git/yap-6.3/pl/swi.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/swi.yap

#false
cat << "EOF" > tmp
/** @pred tabling_statistics/0 


Prints statistics on space used by all tables.



 */
EOF
sed -e "214r tmp" /Users/vsc/git/yap-6.3/pl/tabling.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/tabling.yap

#false
cat << "EOF" > tmp
/** @pred tabling_mode(+ _P_,? _Mode_) 


Sets or reads the default tabling mode for a tabled predicate  _P_
(or a list of predicates  _P1_,..., _Pn_ or
[ _P1_,..., _Pn_]). The list of  _Mode_ options includes:

+ `batched`

    Defines that, by default, batched scheduling is the scheduling
strategy to be used to evaluated calls to predicate  _P_.

+ `local`

    Defines that, by default, local scheduling is the scheduling
strategy to be used to evaluated calls to predicate  _P_.

+ `exec_answers`

    Defines that, by default, when a call to predicate  _P_ is
already evaluated (completed), answers are obtained by executing
compiled WAM-like code directly from the trie data
structure. This reduces the loading time when backtracking, but
the order in which answers are obtained is undefined.

+ `load_answers`
  
   Defines that, by default, when a call to predicate  _P_ is
already evaluated (completed), answers are obtained (as a
consumer) by loading them from the trie data structure. This
guarantees that answers are obtained in the same order as they
were found. Somewhat less efficient but creates less choice-points.

The default tabling mode for a new tabled predicate is `batched`
and `exec_answers`. To set the tabling mode for all predicates at
once you can use the yap_flag/2 predicate as described next.
 
*/
EOF
sed -e "165r tmp" /Users/vsc/git/yap-6.3/pl/tabling.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/tabling.yap

#false
cat << "EOF" > tmp
/** @pred table_statistics(+ _P_) 


Prints table statistics (subgoals and answers) for predicate  _P_
(or a list of predicates  _P1_,..., _Pn_ or
[ _P1_,..., _Pn_]).

 
*/
EOF
sed -e "165r tmp" /Users/vsc/git/yap-6.3/pl/tabling.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/tabling.yap

#false
cat << "EOF" > tmp
/** @pred table( + _P_ )


Declares predicate  _P_ (or a list of predicates
 _P1_,..., _Pn_ or [ _P1_,..., _Pn_]) as a tabled
predicate.  _P_ must be written in the form
 _name/arity_. Examples:

~~~~~
:- table son/3.
:- table father/2.
:- table mother/2.
~~~~~
 or

~~~~~
:- table son/3, father/2, mother/2.
~~~~~
 or

~~~~~
:- table [son/3, father/2, mother/2].
~~~~~

 
*/
EOF
sed -e "165r tmp" /Users/vsc/git/yap-6.3/pl/tabling.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/tabling.yap

#false
cat << "EOF" > tmp
/** @pred show_table(+ _P_) 


Prints table contents (subgoals and answers) for predicate  _P_
(or a list of predicates  _P1_,..., _Pn_ or
[ _P1_,..., _Pn_]).

 
*/
EOF
sed -e "165r tmp" /Users/vsc/git/yap-6.3/pl/tabling.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/tabling.yap

#false
cat << "EOF" > tmp
/** @pred is_tabled(+ _P_) 


Succeeds if the predicate  _P_ (or a list of predicates
 _P1_,..., _Pn_ or [ _P1_,..., _Pn_]), of the form
 _name/arity_, is a tabled predicate.

 
*/
EOF
sed -e "165r tmp" /Users/vsc/git/yap-6.3/pl/tabling.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/tabling.yap

#false
cat << "EOF" > tmp
/** @pred abolish_table(+ _P_) 


Removes all the entries from the table space for predicate  _P_ (or
a list of predicates  _P1_,..., _Pn_ or
[ _P1_,..., _Pn_]). The predicate remains as a tabled predicate.

 
*/
EOF
sed -e "165r tmp" /Users/vsc/git/yap-6.3/pl/tabling.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/tabling.yap

#false
cat << "EOF" > tmp
/** @pred thread_local( _+Functor/Arity_)  


related to the dynamic/1 directive.  It tells the system that the
predicate may be modified using assert/1, retract/1,
etc, during execution of the program.  Unlike normal shared dynamic
data however each thread has its own clause-list for the predicate.
As a thread starts, this clause list is empty.  If there are still
clauses as the thread terminates these are automatically reclaimed by
the system.  The `thread_local` property implies
the property `dynamic`.

Thread-local dynamic predicates are intended for maintaining
thread-specific state or intermediate results of a computation.

It is not recommended to put clauses for a thread-local predicate into
a file as in the example below as the clause is only visible from the
thread that loaded the source-file.  All other threads start with an
empty clause-list.

~~~~~
:- thread_local
    foo/1.

foo(gnat).
~~~~~




 */
EOF
sed -e "1357r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_sleep(+ _Time_) 


Make current thread sleep for  _Time_ seconds.  _Time_ may be an
integer or a floating point number. When time is zero or a negative value 
the call succeeds and returns immediately. This call should not be used if
alarms are also being used.



 */
EOF
sed -e "1266r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_peek_message(+ _Queue_, ? _Term_)

As thread_peek_message/1, operating on a given queue. It is allowed to
peek into another thread's message queue, an operation that can be used
to check whether a thread has swallowed a message sent to it.



Explicit message queues are designed with the <em>worker-pool</em> model
in mind, where multiple threads wait on a single queue and pick up the
first goal to execute.  Below is a simple implementation where the
workers execute arbitrary Prolog goals.  Note that this example provides
no means to tell when all work is done. This must be realised using
additional synchronisation.

~~~~~
%    create_workers(+Id, +N)
%    
%    Create a pool with given Id and number of workers.

create_workers(Id, N) :-
    message_queue_create(Id),
    forall(between(1, N, _),
           thread_create(do_work(Id), _, [])).

do_work(Id) :-
    repeat,
      thread_get_message(Id, Goal),
      (   catch(Goal, E, print_message(error, E))
      ->  true
      ;   print_message(error, goal_failed(Goal, worker(Id)))
      ),
    fail.

%    work(+Id, +Goal)
%    
%    Post work to be done by the pool

work(Id, Goal) :-
    thread_send_message(Id, Goal).
~~~~~


 */
EOF
sed -e "1228r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_peek_message(? _Term_) 


Examines the thread message-queue and compares the queued terms
with  _Term_ until one unifies or the end of the queue has been
reached.  In the first case the call succeeds (possibly instantiating
 _Term_.  If no term from the queue unifies this call fails.

 
*/
EOF
sed -e "1180r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_get_message(+ _Queue_, ? _Term_)

As thread_get_message/1, operating on a given queue. It is allowed to
peek into another thread's message queue, an operation that can be used
to check whether a thread has swallowed a message sent to it.

 
*/
EOF
sed -e "1161r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_get_message(? _Term_) 


Examines the thread message-queue and if necessary blocks execution
until a term that unifies to  _Term_ arrives in the queue.  After
a term from the queue has been unified unified to  _Term_, the
term is deleted from the queue and this predicate returns.

Please note that not-unifying messages remain in the queue.  After
the following has been executed, thread 1 has the term `gnu`
in its queue and continues execution using  _A_ is `gnat`.

~~~~~
   <thread 1>
   thread_get_message(a(A)),

   <thread 2>
   thread_send_message(b(gnu)),
   thread_send_message(a(gnat)),
~~~~~

See also thread_peek_message/1.

 
*/
EOF
sed -e "1149r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_send_message(+ _QueueOrThreadId_, + _Term_)

Place  _Term_ in the given queue or default queue of the indicated
thread (which can even be the message queue of itself (see
thread_self/1). Any term can be placed in a message queue, but note that
the term is copied to the receiving thread and variable-bindings are
thus lost. This call returns immediately.

If more than one thread is waiting for messages on the given queue and
at least one of these is waiting with a partially instantiated
 _Term_, the waiting threads are <em>all</em> sent a wakeup signal,
starting a rush for the available messages in the queue.  This behaviour
can seriously harm performance with many threads waiting on the same
queue as all-but-the-winner perform a useless scan of the queue. If
there is only one waiting thread or all waiting threads wait with an
unbound variable an arbitrary thread is restarted to scan the queue.




 
*/
EOF
sed -e "1116r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred message_queue_destroy(+ _Queue_) 


Destroy a message queue created with message_queue_create/1.  It is
<em>not</em> allows to destroy the queue of a thread.  Neither is it
allowed to destroy a queue other threads are waiting for or, for
anonymous message queues, may try to wait for later.

 
*/
EOF
sed -e "1047r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred message_queue_create(? _Queue_) 


If  _Queue_ is an atom, create a named queue.  To avoid ambiguity
on `thread_send_message/2`, the name of a queue may not be in use
as a thread-name.  If  _Queue_ is unbound an anonymous queue is
created and  _Queue_ is unified to its identifier.

 
*/
EOF
sed -e "1029r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred current_mutex(? _MutexId_, ? _ThreadId_, ? _Count_) 


Enumerates all existing mutexes.  If the mutex is held by some thread,
 _ThreadId_ is unified with the identifier of the holding thread and
 _Count_ with the recursive count of the mutex. Otherwise,
 _ThreadId_ is `[]` and  _Count_ is 0.



 */
EOF
sed -e "945r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred mutex_unlock_all 


Unlock all mutexes held by the current thread.  This call is especially
useful to handle thread-termination using abort/0 or exceptions.  See
also thread_signal/2.

 
*/
EOF
sed -e "916r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_statistics(+ _Id_, + _Key_, - _Value_) 


Obtains statistical information on thread  _Id_ as `statistics/2`
does in single-threaded applications.  This call returns all keys
of `statistics/2`, although only information statistics about the
stacks and CPU time yield different values for each thread.

+ mutex_statistics 


Print usage statistics on internal mutexes and mutexes associated
with dynamic predicates.  For each mutex two numbers are printed:
the number of times the mutex was acquired and the number of
collisions: the number times the calling thread has to
wait for the mutex.  The collision-count is not available on
Windows as this would break portability to Windows-95/98/ME or
significantly harm performance.  Generally collision count is
close to zero on single-CPU hardware.

+ threads 


Prints a table of current threads and their status.



 */
EOF
sed -e "807r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_property(? _Id_, ? _Property_) 


Enumerates the properties of the specified thread.
Calling thread_property/2 does not influence any thread.  See also
thread_join/2.  For threads that have an alias-name, this name can
be used in  _Id_ instead of the numerical thread identifier.
 _Property_ is one of:

+ status( _Status_)
The thread status of a thread (see below).

+ alias( _Alias_)
The thread alias, if it exists.

+ at_exit( _AtExit_)
The thread exit hook, if defined (not available if the thread is already terminated).

+ detached( _Boolean_)
The detached state of the thread.

+ stack( _Size_)
The thread stack data-area size.

+ trail( _Size_)
The thread trail data-area size.

+ system( _Size_)
The thread system data-area size.


 
*/
EOF
sed -e "673r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred current_thread(+ _Id_, - _Status_) 


Enumerates identifiers and status of all currently known threads.
Calling current_thread/2 does not influence any thread.  See also
thread_join/2.  For threads that have an alias-name, this name is
returned in  _Id_ instead of the numerical thread identifier.
 _Status_ is one of:

+ running
The thread is running.  This is the initial status of a thread.  Please
note that threads waiting for something are considered running too.

+ false
The  _Goal_ of the thread has been completed and failed.

+ true
The  _Goal_ of the thread has been completed and succeeded.

+ exited( _Term_)
The  _Goal_ of the thread has been terminated using thread_exit/1
with  _Term_ as argument.  If the underlying native thread has
exited (using pthread_exit())  _Term_ is unbound.

+ exception( _Term_)
The  _Goal_ of the thread has been terminated due to an uncaught
exception (see throw/1 and catch/3).


 
*/
EOF
sed -e "624r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_exit(+ _Term_) 


Terminates the thread immediately, leaving `exited( _Term_)` as
result-state for thread_join/2.  If the thread has the attribute
`detached` `true` it terminates, but its exit status cannot be
retrieved using thread_join/2 making the value of  _Term_
irrelevant.  The Prolog stacks and C-thread are reclaimed.

 
*/
EOF
sed -e "537r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_join(+ _Id_, - _Status_) 


Wait for the termination of thread with given  _Id_.  Then unify the
result-status of the thread with  _Status_.  After this call,
 _Id_ becomes invalid and all resources associated with the thread
are reclaimed.  Note that threads with the attribute `detached`
`true` cannot be joined.  See also current_thread/2.

A thread that has been completed without thread_join/2 being
called on it is partly reclaimed: the Prolog stacks are released and the
C-thread is destroyed. A small data-structure representing the
exit-status of the thread is retained until thread_join/2 is called on
the thread.  Defined values for  _Status_ are:

+ true
The goal has been proven successfully.

+ false
The goal has failed.

+ exception( _Term_)
The thread is terminated on an
exception.  See print_message/2 to turn system exceptions into
readable messages.

+ exited( _Term_)
The thread is terminated on thread_exit/1 using the argument  _Term_.


+ thread_detach(+ _Id_) 


Switch thread into detached-state (see `detached` option at
thread_create/3 at runtime.   _Id_ is the identifier of the thread
placed in detached state.

One of the possible applications is to simplify debugging. Threads that
are created as `detached` leave no traces if they crash. For
not-detached threads the status can be inspected using
current_thread/2.  Threads nobody is waiting for may be created
normally and detach themselves just before completion.  This way they
leave no traces on normal completion and their reason for failure can be
inspected.

 
*/
EOF
sed -e "496r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#true
cat << "EOF" > tmp
/** @pred thread_self(- _Id_) 


Get the Prolog thread identifier of the running thread.  If the thread
has an alias, the alias-name is returned.

 
*/
EOF
sed -e "441r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_signal(+ _ThreadId_, : _Goal_) 


Make thread  _ThreadId_ execute  _Goal_ at the first
opportunity.  In the current implementation, this implies at the first
pass through the <em>Call-port</em>. The predicate thread_signal/2
itself places  _Goal_ into the signalled-thread's signal queue
and returns immediately.

Signals (interrupts) do not cooperate well with the world of
multi-threading, mainly because the status of mutexes cannot be
guaranteed easily.  At the call-port, the Prolog virtual machine
holds no locks and therefore the asynchronous execution is safe.

 _Goal_ can be any valid Prolog goal, including throw/1 to make
the receiving thread generate an exception and trace/0 to start
tracing the receiving thread.




 */
EOF
sed -e "85r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_create(: _Goal_, - _Id_)


Create a new Prolog thread using default options. See thread_create/3.

 
*/
EOF
sed -e "85r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_create(: _Goal_)


Create a new Prolog detached thread using default options. See thread_create/3.

 
*/
EOF
sed -e "85r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred thread_at_exit(: _Term_) 


Run  _Goal_ just before releasing the thread resources. This is to
be compared to `at_halt/1`, but only for the current
thread. These hooks are ran regardless of why the execution of the
thread has been completed. As these hooks are run, the return-code is
already available through thread_property/2 using the result of
thread_self/1 as thread-identifier. If you want to guarantee the 
execution of an exit hook no matter how the thread terminates (the thread 
can be aborted before reaching the thread_at_exit/1 call), consider
using instead the `at_exit/1` option of thread_create/3. 

 
*/
EOF
sed -e "85r tmp" /Users/vsc/git/yap-6.3/pl/threads.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/threads.yap

#false
cat << "EOF" > tmp
/** @pred  user:unknown_predicate_handler(+G,+M,?NG) 


The user may also define clauses for
`user:unknown_predicate_handler/3` hook predicate. This
user-defined procedure is called before any system processing for the
undefined procedure, with the first argument  _G_ set to the current
goal, and the second  _M_ set to the current module. The predicate
 _G_ will be called from within the user module.

If `user:unknown_predicate_handler/3` succeeds, the system will
execute  _NG_. If  `user:unknown_predicate_handler/3` fails, the
system will execute default action as specified by unknown/2.

 
*/
EOF
sed -e "105r tmp" /Users/vsc/git/yap-6.3/pl/undefined.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/undefined.yap

#false
cat << "EOF" > tmp
/** @pred  unknown(- _O_,+ _N_) 


Specifies an handler to be called is a program tries to call an
undefined static procedure  _P_.

The arity of  _N_ may be zero or one. If the arity is `0`, the
new action must be one of `fail`, `warning`, or
`error`. If the arity is `1`,  _P_ is an user-defined
handler and at run-time, the argument to the handler  _P_ will be
unified with the undefined goal. Note that  _N_ must be defined prior
to calling unknown/2, and that the single argument to  _N_ must
be unbound.

In YAP, the default action is to `fail` (note that in the ISO
Prolog standard the default action is `error`).

After defining `undefined/1` by:

~~~~~{.prolog}
undefined(A) :- format('Undefined predicate: ~w~n',[A]), fail.
~~~~~
and executing the goal:

~~~~~{.prolog}
unknown(U,undefined(X)).
~~~~~
a call to a predicate for which no clauses were defined will result in
the output of a message of the form:

~~~~~{.prolog}
Undefined predicate: user:xyz(A1,A2)
~~~~~
followed by the failure of that call.

 
*/
EOF
sed -e "73r tmp" /Users/vsc/git/yap-6.3/pl/undefined.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/undefined.yap

#false
cat << "EOF" > tmp
/** @pred  subsumes_term(? _Subsumer_, ? _Subsumed_) 



Succeed if  _Submuser_ subsumes  _Subsuned_ but does not bind any
variable in  _Subsumer_.

 
*/
EOF
sed -e "403r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred nb_current(? _Name_,? _Value_) 


Enumerate all defined variables with their value. The order of
enumeration is undefined.

 
*/
EOF
sed -e "370r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred  nb_current(? _Name_, ? _Value_)  


Enumerate all defined variables with their value. The order of
enumeration is undefined. 

 
*/
EOF
sed -e "370r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred  nth_instance(? _Key_,? _Index_, _T_,? _R_)

Fetches the  _Index_nth entry in the internal database under the key
 _Key_. Entries are numbered from one. If the key  _Key_ or the
 _Index_ are bound, a reference is unified with  _R_. Otherwise,
the reference  _R_ must be given, and YAP will find
the matching key and index.

 
*/
EOF
sed -e "346r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred  nth_instance(? _Key_,? _Index_,? _R_) 


Fetches the  _Index_nth entry in the internal database under the key
 _Key_. Entries are numbered from one. If the key  _Key_ or the
 _Index_ are bound, a reference is unified with  _R_. Otherwise,
the reference  _R_ must be given, and YAP will find
the matching key and index.

 
*/
EOF
sed -e "329r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#true
cat << "EOF" > tmp
/** @pred  simple( _T_) 


Checks whether  _T_ is unbound, an atom, or a number.

 
*/
EOF
sed -e "314r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred  callable( _T_) is iso 


Checks whether  _T_ is a callable term, that is, an atom or a
compound term.

 
*/
EOF
sed -e "304r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred  recordzifnot(+ _K_, _T_,- _R_) 


If a term equal to  _T_ up to variable renaming is stored under key
 _K_ fail. Otherwise, make term  _T_ the first record under key
 _K_ and unify  _R_ with its reference.

This predicate is YAP specific.

 
*/
EOF
sed -e "288r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred  recordaifnot(+ _K_, _T_,- _R_) 


If a term equal to  _T_ up to variable renaming is stored under key
 _K_ fail. Otherwise, make term  _T_ the first record under key
 _K_ and unify  _R_ with its reference.

 
*/
EOF
sed -e "269r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred current_op( _P_, _T_, _F_) is iso 


Defines the relation:  _P_ is a currently defined  operator of type
 _T_ and precedence  _P_.

 
*/
EOF
sed -e "169r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred op(+ _P_,+ _T_,+ _A_) is iso 


Defines the operator  _A_ or the list of operators  _A_ with type
 _T_ (which must be one of `xfx`, `xfy`,`yfx`,
`xf`, `yf`, `fx` or `fy`) and precedence  _P_
(see appendix iv for a list of predefined operators).

Note that if there is a preexisting operator with the same name and
type, this operator will be discarded. Also, `,` may not be defined
as an operator, and it is not allowed to have the same for an infix and
a postfix operator.

 
*/
EOF
sed -e "49r tmp" /Users/vsc/git/yap-6.3/pl/utils.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/utils.yap

#false
cat << "EOF" > tmp
/** @pred  stream_position_data(+ _Field_,+ _StreamPosition_,- _Info_) 


Given the packaged stream position term  _StreamPosition_, unify
 _Info_ with  _Field_ `line_count`, `byte_count`, or
`char_count`.




 */
EOF
sed -e "550r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#true
cat << "EOF" > tmp
/** @pred  current_stream( _F_, _M_, _S_) 


Defines the relation: The stream  _S_ is opened on the file  _F_
in mode  _M_. It might be used to obtain all open streams (by
backtracking) or to access the stream for a file  _F_ in mode
 _M_, or to find properties for a stream  _S_. Notice that some
streams might not be associated to a file: in this case YAP tries to
return the file number. If that is not available, YAP unifies  _F_
with  _S_.

 
*/
EOF
sed -e "489r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  current_char_conversion(? _IN_,? _OUT_) is iso 


If  _IN_ is unbound give all current character
translations. Otherwise, give the translation for  _IN_, if one
exists.

 
*/
EOF
sed -e "463r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  stream_position(+ _Stream_,- _StreamPosition_) 


Unify  _StreamPosition_ with the packaged information of position on
current stream  _Stream_. Use stream_position_data/3 to
retrieve information on character or line count.

 
*/
EOF
sed -e "423r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  current_line_number(+ _Stream_,- _LineNumber_)

Unify  _LineNumber_ with the line number for the  _Stream_. 

 
*/
EOF
sed -e "413r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  ttynl 


Outputs a new line to stream user_output.




 */
EOF
sed -e "392r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  ttyput(+ _N_) 


As `put(N)` but always to user_output.

 
*/
EOF
sed -e "384r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  ttyskip(- _C_) 


Like skip/1, but always using stream user_input.
stream.

 
*/
EOF
sed -e "375r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  ttyget0(- _C_) 


The same as `get0(C)`, but from stream user_input.

 
*/
EOF
sed -e "365r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  ttyget(- _C_) 


The same as `get(C)`, but from stream user_input.

 
*/
EOF
sed -e "356r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  format(+ _T_)

Print formatted output to the current output stream.

 
*/
EOF
sed -e "339r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  display(+ _S_, _T_)

Like display/1, but using stream  _S_ to display the term.

 
*/
EOF
sed -e "318r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#true
cat << "EOF" > tmp
/** @pred  display(+ _T_) 


Displays term  _T_ on the current output stream. All Prolog terms are
written in standard parenthesized prefix notation.

 
*/
EOF
sed -e "308r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  read(+ _S_,- _T_) is iso

Reads term  _T_ from the stream  _S_ instead of from the current input
stream.

 
*/
EOF
sed -e "283r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  read(- _T_) is iso 


Reads the next term from the current input stream, and unifies it with
 _T_. The term must be followed by a dot (`.`) and any blank-character
as previously defined. The syntax of the term must match the current
declarations for operators (see op). If the end-of-stream is reached, 
 _T_ is unified with the atom `end_of_file`. Further reads from of 
the same stream may cause an error failure (see open/3).

*/
EOF
sed -e "273r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  exists(+ _F_) 


Checks if file  _F_ exists in the current directory.

*/
EOF
sed -e "255r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  nofileerrors 


Switches off the file_errors flag, so that the predicates see/1,
tell/1, open/3 and close/1 just fail, instead of producing
an error message and aborting whenever the specified file cannot be
opened or closed.

*/
EOF
sed -e "248r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/**  @pred fileerrors 


Switches on the file_errors flag so that in certain error conditions
Input/Output predicates will produce an appropriated message and abort.

 */
EOF
sed -e "238r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  socket_connect(+ _SOCKET_, + _PORT_, - _STREAM_) 



Interface to system call `connect`, used for clients: connect
socket  _SOCKET_ to  _PORT_. The connection results in the
read/write stream  _STREAM_.

Port information depends on the domain:

+ 'AF_UNIX'(+ _FILENAME_)
+ 'AF_FILE'(+ _FILENAME_)
connect to socket at file  _FILENAME_.

+ 'AF_INET'(+ _HOST_,+ _PORT_)
Connect to socket at host  _HOST_ and port  _PORT_.


 
*/
EOF
sed -e "201r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  socket(+ _DOMAIN_,+ _TYPE_,+ _PROTOCOL_,- _SOCKET_) 


Corresponds to the BSD system call `socket`. Create a socket for
domain  _DOMAIN_ of type  _TYPE_ and protocol
 _PROTOCOL_. Both  _DOMAIN_ and  _TYPE_ should be atoms,
whereas  _PROTOCOL_ must be an integer.
The new socket object is
accessible through a descriptor bound to the variable  _SOCKET_.

The current implementation of YAP  accepts socket
domains `AF_INET` and `AF_UNIX`. 
Socket types depend on the
underlying operating system, but at least the following types are
supported: `SOCK_STREAM'` and `SOCK_DGRAM'` (untested in 6.3).

 
*/
EOF
sed -e "171r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred  socket(+ _DOMAIN_,- _SOCKET_)


Call socket/4 with  _TYPE_ bound to `SOCK_STREAM'` and
 _PROTOCOL_ bound to `0`.

 
*/
EOF
sed -e "144r tmp" /Users/vsc/git/yap-6.3/pl/yio.yap > x
     mv x /Users/vsc/git/yap-6.3/pl/yio.yap

#false
cat << "EOF" > tmp
/** @pred free_variables(:Generator, + _Template_, +VarList0, -VarList)  is det


In order to handle variables properly, we have to find all the universally quantified variables in the Generator. All variables as yet unbound are universally quantified, unless

+ they occur in the template
+ they are bound by X/\P, setof, or bagof

`free_variables(Generator, Template, OldList, NewList)` finds this set, using OldList as an accumulator.


The original author of this code was Richard O'Keefe. Jan Wielemaker
made some SWI-Prolog enhancements, sponsored by SecuritEase,
http://www.securitease.com. The code is public domain (from DEC10 library).


 */
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/aggregate.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/aggregate.pl

#false
cat << "EOF" > tmp
/** @pred aggregate_all(+ _Template_, : _Goal_, - _Result_)  is semidet


Aggregate bindings in  _Goal_ according to  _Template_. The
aggregate_all/3 version performs findall/3 on  _Goal_.
 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/aggregate.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/aggregate.pl

#false
cat << "EOF" > tmp
/** @pred aggregate_all(+ _Template_, + _Discriminator_, : _Goal_, - _Result_) is semidet

Aggregate bindings in  _Goal_ according to  _Template_. The
aggregate_all/3 version performs findall/3 followed by sort/2 on
 _Goal_.
 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/aggregate.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/aggregate.pl

#false
cat << "EOF" > tmp
/** @pred read_stream_to_codes(+ _Stream_, - _Codes_, ? _Tail_)

Difference-list version of read_stream_to_codes/2.

 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/readutil.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/readutil.pl

#false
cat << "EOF" > tmp
/** @pred read_stream_to_codes(+ _Stream_, - _Codes_) 


Read all input until end-of-file and unify the result to  _Codes_.

 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/readutil.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/readutil.pl

#false
cat << "EOF" > tmp
/** @pred read_line_to_codes(+ _Stream_, - _Codes_, ? _Tail_)

Difference-list version to read an input line to a list of character
codes.  Reading stops at the newline or end-of-file character, but
unlike read_line_to_codes/2, the newline is retained in the
output.  This predicate is especially useful for reading a block of
lines upto some delimiter.  The following example reads an HTTP header
ended by a blank line:

~~~~~
read_header_data(Stream, Header) :-
    read_line_to_codes(Stream, Header, Tail),
    read_header_data(Header, Stream, Tail).

read_header_data("\r\n", _, _) :- !.
read_header_data("\n", _, _) :- !.
read_header_data("", _, _) :- !.
read_header_data(_, Stream, Tail) :-
    read_line_to_codes(Stream, Tail, NewTail),
    read_header_data(Tail, Stream, NewTail).
~~~~~

 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/readutil.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/readutil.pl

#false
cat << "EOF" > tmp
/** @pred read_line_to_codes(+ _Stream_, - _Codes_) 



Read the next line of input from  _Stream_ and unify the result with
 _Codes_ <em>after</em> the line has been read.  A line is ended by a
newline character or end-of-file. Unlike `read_line_to_codes/3`,
this predicate removes trailing newline character.

On end-of-file the atom `end_of_file` is returned.  See also
`at_end_of_stream/[0,1]`.

 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/readutil.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/readutil.pl

#false
cat << "EOF" > tmp
/** @pred read_file_to_terms(+ _Spec_, - _Terms_, + _Options_) 


Read a file to a list of Prolog terms (see read/1). @c  _Spec_ is a









 */
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/readutil.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/readutil.pl

#false
cat << "EOF" > tmp
/** @pred read_file_to_codes(+ _Spec_, - _Codes_, + _Options_) 


Read a file to a list of character codes. Currently ignores
 _Options_.

 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/readutil.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/readutil.pl

#false
cat << "EOF" > tmp
/** @pred use_foreign_library(+ _FileSpec_) is det
     use_foreign_library(+ _FileSpec_, + _Entry_:atom) is det



Load and install a foreign library as load_foreign_library/1
and `load_foreign_library/2` and
register the installation using `initialization/2` with the option
now. This is similar to using:

~~~~~
    :- initialization(load_foreign_library(foreign(mylib))).
~~~~~

but using the initialization/1 wrapper causes the library to
be loaded after loading of the file in which it appears is
completed, while use_foreign_library/1 loads the library
immediately. I.e. the difference is only relevant if the remainder
of the file uses functionality of the `C`-library. 

 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/shlib.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/shlib.pl

#false
cat << "EOF" > tmp
/** @pred unload_foreign_library(+ _FileSpec_, + _Exit_:atom)  is det




Unload a shared
object or DLL. After calling the  _Exit_ function, the shared object is
removed from the process. The default exit function is composed from
`uninstall_`, followed by the file base-name.

 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/shlib.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/shlib.pl

#false
cat << "EOF" > tmp
/** @pred unload_foreign_library(+ _FileSpec_) is det
 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/shlib.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/shlib.pl

#false
cat << "EOF" > tmp
/** @pred load_foreign_library(: _FileSpec_, + _Entry_:atom) is det

Load a shared object or DLL. After loading the  _Entry_ function is
called without arguments. The default entry function is composed
from `install_`, followed by the file base-name. E.g., the
load-call below calls the function `install_mylib()`. If the platform
prefixes extern functions with `_`, this prefix is added before
calling.

~~~~~
          ...
          load_foreign_library(foreign(mylib)),
          ...
~~~~~

 _FileSpec_ is a specification for
absolute_file_name/3. If searching the file fails, the plain
name is passed to the OS to try the default method of the OS for
locating foreign objects. The default definition of
file_search_path/2 searches <prolog home>/lib/Yap.

See also
`use_foreign_library/1,2` are intended for use in
directives. 

 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/shlib.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/shlib.pl

#false
cat << "EOF" > tmp
/** @pred load_foreign_library(: _FileSpec_) is det 


 
*/
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/shlib.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/shlib.pl

#false
cat << "EOF" > tmp
/** @pred current_foreign_library(? _File_, ? _Public_)  



Query currently
loaded shared libraries.  




 */
EOF
sed -e "31r tmp" /Users/vsc/git/yap-6.3/swi/library/shlib.pl > x
     mv x /Users/vsc/git/yap-6.3/swi/library/shlib.pl

