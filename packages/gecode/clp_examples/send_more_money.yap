%% -*- prolog -*-
%%=============================================================================
%% Copyright (C) 2011, 2013 by Denys Duchier, Vitor Santos Costa
%%
%% This program is free software: you can redistribute it and/or modify it
%% under the terms of the GNU Lesser General Public License as published by the
%% Free Software Foundation, either version 3 of the License, or (at your
%% option) any later version.
%% 
%% This program is distributed in the hope that it will be useful, but WITHOUT
%% ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
%% FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
%% more details.
%% 
%% You should have received a copy of the GNU Lesser General Public License
%% along with this program.  If not, see <http://www.gnu.org/licenses/>.
%%=============================================================================

:- use_module(library(gecode/clpfd)).

%   S E N D
% + M O R E
% ---------
% M O N E Y
send_more_money(Letters) :-
	[S,E,N,D,M,O,R,Y] = Letters,
	Letters ins 0..9,
	M #\= 0,
	S #\= 0,
	all_distinct(Letters),
	          1000*S + 100*E + 10*N + D +
                  1000*M + 100*O + 10*R + E #=
        10000*M + 1000*O + 100*N + 10*E + Y,
	labeling([], Letters).
