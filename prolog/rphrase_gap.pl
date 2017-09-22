:- module(rphrase,
	[	rphrase/3         % probabilistic DCG interpreter
	,	run_rphrase/5     % run rphrase in ordinary DCG with given states
	,	sample_rphrase/4  % sample a sequence from pDCG
	,	sample_goal/3     % sample a sequence from pDCG
	,	resample_probs/3  % modify probabilities behind pDCG
	,	cool_probs/3 		% make probabilities have lower entropy
	,	edit_probs/4  		% explicit modification of probabilities
	,	product_probs/3   % multiply pairs of models
	,	empty_state/1  	% reset to empty probability tables
	,	load_rules/1 		% assert pDCG rules from given module
	,	tron/0, troff/0, tron/1 % control execution tracing

	,	op(1200,xfx,--->)
	,	op(1200,xfx,+-->)
	,	op(1180,xfx,\\)
	,	op(1190,xfx,#)
	,	op(900,fx,#)
	]).

/** <module> - Probabilistic DCG sampler

A DCG meta-interpreter that maintains a probability distribution
for each choice point and makes a random decision when interpreting
a phrase. 

Probabilistic DCG rules are defined using --->/2 and +-->/2,
which work like ordinary DCG rules except that whenever multiple
clauses are available, the interpreter makes a random choice.
It also interprets #Goal to mean _|find all the solutions of Goal
and choose one of them at random|_.

The distributions are kept in a big list indexed by
a sort of generalised head term, and this structure is threaded through
the sampling sequence. The state of the model is represented by
a term of type =pdcg=, where

==
pdcg        ---> pdcg(list(ruledef(soln)),list(ruledef(clause))).
ruledef(A)  ---> rule(term,list(weighted(A))).
weighted(A) ---> float-A.
soln        ---> soln(term).
clause      ---> clause(term).
==


Uses matching_solns written in Prolog
Uses list sampler written in Prolog

@tbd
Try to optimise representation of discrete distribution:
list vs. big term vs foreign object. See GSL.

@author Samer Abdallah

@version 0.2

@license GPL
*/

:- meta_predicate sample_goal(:,?,?).	

:- module_transparent 
		rphrase/3 
	,	run_rphrase/5
	,	sample_rphrase/4
	,	sample_goal/3
	.

:- use_module(library(plrand)).
:- use_module(library(prob/meta)).
:- use_module(library(callutils), [bt_call/2]).
:- use_module(library(dcg_core), [out//1, set//1, get//1, set_with//1, repeat//0, nop//0, once//1]). 
:- use_module(library(dcg_pair)). 

:- op(1200,xfx,--->).
:- op(1200,xfx,+-->).
:-	op(1050,xfy,>>).
:- op(1190,xfx,#).
:-	op(900,fx,#).
:- op(1180,xfx,\\).


:- multifile (--->)/2, (+-->)/2.
:- multifile maprule/2, mapgoal/2.
:- dynamic (--->)/2, (+-->)/2.
:- dynamic maprule/2, mapgoal/2.

% tracer messages
:- dynamic rtrace/2.


%% --->(Head,Body) is nondet.
%% +-->(Head,Body) is nondet.
%
%  The user can declare grammar rules by adding clauses of these 
%  predicates. They can either be declared directly in the rhprase module, eg:
%  
%  ==
%  rphrase: (sentence ---> noun_phrase, verb_phrase).
%  ==
%
%  or an other module and imported using load_rules/1, eg:
%
%  ==
%  english: (sentence ---> noun_phrase, verb_phrase).
%  init :- load_rules(english).
%  ==
%
%  The (+-->)/2 form must be used for recursive rules as it enables
%  a mechanism to stop infinite recursion, eg:
%
%  ==
%  noun ---> nominal.
%  noun +--> adjective, noun.
%  ==

%% mapgoal( Head1, Head2) is nondet.
%% maprule( Head1, Head2) is nondet.
%
%  User defined predicates for deciding which forms of a given head term
%  will get their own independent probability distributions over their
%  solutions or clauses. A goal that unifies with Head1 will be mapped to Head2
%  before looking up matching definitions in the probability tables,
%  or creating a new table if Head2 does not exist yet.
%
%  For example, suppose we have a Prolog predicate noun/2 which holds
%  a set of nouns which may refer to discrete objects or continuous
%  substances, eg
%  ==
%  noun( continuous, water).
%  noun( continuous, salt).
%  noun( discrete, atom).
%  noun( discrete, cat).
%  ==
%
%  If  we declare:
%  $ mapgoal( noun(_,_), noun(_,_)).
%  then a query of #noun(Type,Word) will result in a sample
%  from a distribution over all four solutions of noun/2.
%  A query of #noun(continuous,Word) will sample conitionally
%  from the SAME probability distribution, but with the
%  the non-matching entries (for discrete nouns) removed.
%
%  Suppose, however, we declare
%  $ mapgoal( noun(T,_), nount(T,_)).
%  A query of #noun(Type,Word) will result in a sample from
%  a distribution over all four solutions of noun/2 as before.
%  But a query of #noun(continuous,W) will sample from a new
%  and completely independent distribution over the two solutions
%  of noun(continuous,Word). Similarly, #noun(discrete,Word)
%  will sample from a third independent distribution. Thus, there
%  will be THREE completely independent probability distributions
%  labeled by noun(_,_), noun(continuous,_) and noun(discrete,_).
%
%  maprule/2 operates the same way but for pDCG rules and 
%  manages probability tables over matching clauses bodies.

%% load_rules( +Module) is det.
%
%  Make probabilistic DCG rules from named module visible to rphrase.
%  Works by (effectively) importing the predicates maprule/2,
%  mapgoal/2, (--->)/2 and (+-->)/2 from Module to rphrase.

load_rules(Module) :-
	assert( maprule(A,B) :- Module:maprule(A,B)),
	assert( mapgoal(A,B) :- Module:mapgoal(A,B)),
	assert( (A--->B)     :- Module:(A--->B)),
	assert( (A+-->B)     :- Module:(A+-->B)).

%% empty_state( -State:pdcg) is det.
%
%  Initialise State to empty pDCG before any sampling.
empty_state(pdcg([],[])).


%% sample_rphrase( +P:phrase, -L:list, +S1:pdcg, -S2:pdcg) is random.
%
%  Run a pDCG phrase collecting the output in list L.
sample_rphrase(P,L,S1,S2) :- rphrase(P,(L-[])-S1,([]-[])-S2).

%% run_rphrase( +P:phrase, +S1:pdcg, -S2:pdcg)// is random.
%
%  Run rphrase on P inside standard (list building) DCG, taking
%  mode state from S1 to S2.
run_rphrase(P,S1,S2) --> run_right(rphrase(P), S1, S2).


%%	rphrase( +P:phrase, +S1:rpst, -S2:rpst) is random.
%
%  Probabilistic DCG main interpreter.
%  The interpreter state is of type =rpst=, where
%  =|rpst ---> (list,pdcg).|=
%  A pDCG phrase can be any of the following:
%
%		* (P1:phrase,P2:phrase) 
%		  sequential composition. 
%		* (P1:phrase>>P2:phrase) 
%		  sequential composition. 
%		* (phrase->phrase;phrase) 	
%		  if-then-else
%		* (P1:phrase->P2:phrase)  		 
%		  Equivalent to (P1->P2;nop).
%		* fac(P:phrase)		 
%		  Keep retrying until phrase succeeds.
%		* {G:goal}           
%		  Execute Prolog goal.
%		* []               
%		  No operation.
%		* [A|list(A)]      
%		  output symbols
%		* out(A)       	 
%		  output one symbol.
%		* set(S:pdcg)    	 
%		  Set pDCG model.
%		* get(S:pdcg)    
%		  Get pDCG model.
%		* empty         	
%		  Initialise pDCG model.
%		* app(G:goal(2))    
%		  apply G:pred(+pdcg,-pdcg) to current model.
%		* #(G:goal(0))   
%		  #G makes a random choice from all solutions of Prolog goal G.
%		* Head       
%		  For any other phrase, look up clauses matching
%		  the head term and make a random choice according to
%		  the current probabilities.
%
%  Clauses are defined using --->/2 and +-->/2.
%  The procedure which looks up clauses matching a given head term uses the
%  predicates mapgoal/2 and maprule/2.
%  Some predefined rules are:
%
%		* cool(DT:float)
%		  Modify probabilities as in cool_probs/3.
%		* resample(Method)
%		  Modify probabilities as in resample_probs/3.
%		* edit(Head,Method)
%		  Modify probabilities as in edit_probs/4.
%		* rep(N:natural,P:phrase)
%		  run N copies of P sequentially.
%		* iso(P:phrase)
%		  run P without changing the state of the model.
%		* with(S:pdcg,P:phrase)
%		  Run phrase starting using given pDCG model and without changing current model.

rphrase((A,B))  --> !, rphrase(A), rphrase(B).
rphrase(A>>B)   --> !, rphrase(A), rphrase(B).
rphrase(G->A;B) --> !, (rphrase(G) ->	rphrase(A);	rphrase(B)).
rphrase(G->A)   --> !, (rphrase(G) ->	rphrase(A);	nop).
rphrase(fac(G)) --> !, once((repeat,rphrase(G))). % !! dangerous
rphrase({G})    --> !, {once(G)}. 

rphrase([])     --> !.
rphrase([A|AX]) --> !, \< \< [A|AX]. 
rphrase(out(L)) --> !, \< \< out(L).
rphrase(set(S)) --> !, \> set(S).
rphrase(get(S)) --> !, \> get(S).
rphrase(empty)  --> !, \> set_with(empty_state).
rphrase(app(G)) --> !, \> once(G).

rphrase(island(A)) --> !, (\< \> trans(G,G)) // rphrase(A).
rphrase(fills(A,B)) --> !, (\< \> out(A)), rphrase(B).

% capture output of operator
% rphrase(A\\B,L1-S1,L2-S2) :- !, rphrase(A,B-S1,[]-S2), append(B,L2,L1).

% only the following clauses create choice points
% at each choice point, we choose randomly

% execute a goal and choose one of the solutions
rphrase( #(G))  --> !, 
	{rtrace(pre,goal:G)},
	\> sample_goal(G),
	{rtrace(post,goal:G)}.

% expand a DCG rule choosing one of the clauses
rphrase(T)  --> !, 
	{rtrace(pre,rule:T)},
	\> rphrase:sample_rule(T,Body),
	rphrase(Body),
	{rtrace(post,rule:T)}.



mapgoal_x( A, B) :- mapgoal(A,B), !.
mapgoal_x( (A,B), (MA,MB) ) :- !, mapgoal_x(A,MA), mapgoal_x(B,MB).
mapgoal_x( (A;B), (MA;MB) ) :- !, mapgoal_x(A,MA), mapgoal_x(B,MB).
mapgoal_x( (A->B), (MA->MB) ) :- !, mapgoal_x(A,MA), mapgoal_x(B,MB).
mapgoal_x( \+A, \+MA ) :- !, mapgoal_x(A,MA).
mapgoal_x( A\=B, A\=B) :- !.
mapgoal_x( when(A,B), when(A,B)) :- !.
mapgoal_x( atom_concat(A,B,C), atom_concat(A,B,C)) :- !.
mapgoal_x( A, B) :- copy_head(A,B).

maprule_x( A, B) :- maprule(A,B), !.
maprule_x( A, B) :- copy_head(A,B).

dcg_clause(H,true,B,nonrec,1) :- (H ---> B), H\=(_ # _), H\=(_\\_), B\=(_\\_).
dcg_clause(H,true,B,rec,1)    :- (H +--> B), H\=(_ # _), H\=(_\\_), B\=(_\\_).
dcg_clause(H,true,B,nonrec,W) :- (W # H ---> B), H\=(_\\_), B\=(_\\_).
dcg_clause(H,true,B,rec,W)    :- (W # H +--> B), H\=(_\\_), B\=(_\\_).

dcg_clause(H,G,B,nonrec,1) :- (H \\ G ---> B), B\=(_\\_).
dcg_clause(H,G,B,rec,1)    :- (H \\ G +--> B), B\=(_\\_).
dcg_clause(H,G,B,nonrec,W) :- (W # H \\ G ---> B), B\=(_\\_).
dcg_clause(H,G,B,rec,W)    :- (W # H \\ G +--> B), B\=(_\\_).

dcg_clause(H,G,B,nonrec,1) :- (H ---> G \\ B), H\=(_\\_).
dcg_clause(H,G,B,rec,1)    :- (H +--> G \\ B), H\=(_\\_).
dcg_clause(H,G,B,nonrec,W) :- (W # H ---> G \\ B), H\=(_\\_).
dcg_clause(H,G,B,rec,W)    :- (W # H +--> G \\ B), H\=(_\\_).

sample_goal(M:G,pdcg(GS0,RS),pdcg(GS1,RS)) :- !,
	% possibly map goal to something more general
	mapgoal_x(G,G1), 
		
	(	rule_lookup(G1,GS0,Goal,_)
	->	rule_clauses(Goal,Solutions),
		GS1=GS0

	;	% choice point unrecognised - look up all clauses and add
		% this must initialise some discrete distribution over
		% a potentially very large number of choices
		% hence, using plrand, new_rule should be a distribution object
		copy_term(G1,G2),
		setof(1-soln(G2,1),M:G2,Solutions1),
		new_rule(G2,Solutions1,Rule,Solutions), 
		GS1=[Rule|GS0]
	),
	
	% here we must sample from distribution, but rejecting
	% those that don't match the query
	matching_solns(G,Solutions,Dist),
	rtrace(match_check(Dist),goal:G),
	wrandom(Dist,soln(X,_)),
	copy_term(X,G).


sample_rule(T,Body,pdcg(GS,RS0),pdcg(GS,RS1)) :- !,
	% possibly map query to generalised term
	maprule_x(T,T1), 

	(	rule_lookup(T1,RS0,Rule,_)
	->	% found term representing this choice point
		rule_clauses(Rule,Clauses),
		RS1=RS0

	;	% choice point unrecognised - look up all clauses and add
		copy_term(T1,T2),
		setof(W0-clause(T2,Grd,Body,Rec,W0),
			dcg_clause(T2,Grd,Body,Rec,W0),
			Clauses1),
		new_rule(T2,Clauses1,Rule,Clauses), 
		RS1=[Rule|RS0]
	),
	
	matching_solns(T,Clauses,Dist),
	rtrace(match_check(Dist),rule:T),
	adjust_weights(Dist,Dist1),
	wrandom(Dist1,clause(T1,O,B1,_,_)),
	post_unify(O,T1,B1,T,Body).

post_unify(true,T1,B1,T,B) :- copy_term(T1/B1,T/B).
post_unify(copy,T,B,T,B).




/* dynamic Rules/Clauses management
 */

divmeasure(T,W-clause(H,G,B,R,V),W1-clause(H,G,B,R,V1)) :- W1 is W/T,V1 is V/T.
divmeasure(T,W-soln(G,V),W1-soln(G,V1)) :- W1 is W/T, V1 is V/T.

new_rule(Head,C,rule(Head,C3),dist(1,C3)) :- 
	unzipweights(C,_,W,_),
	sumlist(W,T),
	maplist(divmeasure(T),C,C1),
	sort(C1,C2),
	reverse(C2,C3). 

rule_clauses(rule(_Head,Clauses),dist(_,Clauses)).
rule_lookup(Query,Rules,rule(Head,Clauses),N) :-
	nth1(N,Rules,rule(Head,Clauses)), 
	Query=@=Head.


matching_solns(Goal,dist(_,WX),dist(Tot,WX1)) :-
	matching_solns(Goal,WX,WX1,0,Tot).

matching_solns(_,[],[],T,T).
matching_solns(Goal,[W-G|CX],MX,T1,T3) :-
	(	filter_goal(Goal,G,H)
	->	MX=[W-H|MXX], T2 is T1+W
	;	MX=MXX, T2=T1
	),
	matching_solns(Goal,CX,MXX,T2,T3).

filter_goal(Goal,soln(G,_),soln(G,_)) :- !, unifiable(Goal,G,_).
filter_goal(Goal,clause(H,true,B,R,_),clause(H,true,B,R,_)) :- !,unifiable(Goal,H,_).
filter_goal(Goal,clause(H,G,B,R,_),clause(H1,copy,B1,R,_)) :- 
	copy_term(Goal,H1),
	copy_term(c(H,G,B),c(H1,G1,B1)),
	call(G1).

% this makes sure that weights for recursive clauses are not too large
rec_weight_max(0.9).

adjust_weights(dist(Tot,In),dist(NewTot,Out)) :- 
	rec_weight_max(Max1), Max is Max1*Tot,
	adjust_weights_x(Max/Tot,In,Out,0,NewTot).

adjust_weights_x(_,[],[],T,T).

% adjust_weights_x(I,[W-soln(G)|RX],[W-soln(G)|SX],T1,T3) :- T2 is T1+W, adjust_weights_x(I,RX,SX,T2,T3).
%adjust_weights_x(I,[W-clause(H,G,B,nonrec,M)|RX],[W-clause(H,G,B,nonrec,M)|SX],T1,T3) :- T2 is T1+W, adjust_weights_x(I,RX,SX,T2,T3).

adjust_weights_x(Max/Tot,[W-Clause|RX],[W1-Clause|SX],T1,T3) :- 
	Clause=clause(H,_,_,Rec,_),
	(	Rec=nonrec -> W1=W
	;	(	W=<Max -> W1=W 
		;	W1 is Max*(Tot-W)/(Tot-Max),
			functor(H,HF,HA),
			format('limiting ~w/~w :  ~q              \r',[W,Tot,HF/HA]),
			flush_output)),
	T2 is T1+W1,
	adjust_weights_x(Max/Tot,RX,SX,T2,T3).


% wrandom - weighted sampling of things
%
% wrandom(
%    WeightedThings:list(N,term(nonneg-term)) ~'list of N things with weights',
%    nonneg                             ~'total of weights',
%    Thing:term(nonneg-term)            ~'random choice from list'
% ).
%
% mode wrandom(in,out,out) is random.

wrandom(dist(_,[]),_) :- !, fail.
wrandom(dist(_,[_-U]),U) :- !.
wrandom(dist(Tot,WX),U) :-
	plrand:sample_Single_(X), 
	XX is X*Tot,
	cum_test1(XX,WX,U).

cum_test1(_,[_-U],U) :- !.
cum_test1(X,[W1-T1|TX],U) :-
	Y is X-W1,
	(Y<0 -> U=T1; cum_test1(Y,TX,U) ).

% -----------------------------------------------------------------------------------


cool(DT) ---> app(cool_probs(DT)).
resample(Method) ---> app(resample_probs(Method)).
edit(Head,Method) ---> app(edit_probs(Head,Method)).


%% resample_probs( +Method, +S1:pdcg, -S2:pdcg) is random.
%
%  Resample probabilities based on their current values using
%  given method. Method can be:
%
% * dirichlet(Alpha:nonneg)  
%   Sample from Dirichlet distribution.
% * specialise(Mult:nonneg)  
%   Sample from Dirichlet hierarchically based on current measure.
% * diffuse(Mult:nonneg,Rate:noneg,BG:nonneg) 
%   Random perturbation of current distribution.
% * diffuse(Rate:nonneg,BG:nonneg)     
%   Random perturbation of current distribution.
% * diffuse_to(Rate,Mult,BGModel:pdcg) 
%   Random perturbation towards given model.

:- meta_predicate resample_probs(+,+,-).
resample_probs(Method, pdcg(In1,In2), pdcg(Out1,Out2)) :- 
	Method = diffuse_to(Rate,Mult,pdcg(Bg1-_,Bg2-_)), !,
	maplist(rule_resample(diffuse_to(Rate,Mult)),Bg1,In1,Out1),
	maplist(rule_resample(diffuse_to(Rate,Mult)),Bg2,In2,Out2).

resample_probs(Method, pdcg(In1,In2), pdcg(Out1,Out2)) :- 
	maplist(rule_resample(rphrase:Method),In1,Out1),
	maplist(rule_resample(rphrase:Method),In2,Out2).


%% product_probs( +S1:pdcg, +S2:pdcg, -S3:pdcg) is det.
%
%  Take two isomorphic models and multiply their probability
%  distributions to get a new model.

product_probs( pdcg(K1,K2), pdcg(In1,In2), pdcg(Out1,Out2)) :- 
	maplist(rule_product,K1,In1,Out1),
	maplist(rule_product,K2,In2,Out2).


%% cool_probs( +DT:float, +S1:pdcg, -S2:pdcg) is det.
%
%  Raises or lowers 'temperature' of all probability distributions.
%  Probabilities are raised to a power and then renormalised.

cool_probs(DT, pdcg(In1,In2), pdcg(Out1,Out2)) :-
	K is 1/DT,
	maplist(rule_cool(K),In1,Out1),
	maplist(rule_cool(K),In2,Out2).


%% edit_probs( +Spec, +Method, +S1:pdcg, -S2:pdcg) is det.
%
%  Edit model probabilities. Spec is one of goal:Head or rule:Head,
%  where Head matches the head of the rule or goal being edited.
%  Method can be one of
%  * print
%  * print_head
%  * print_all
%  * get_weights(H,W)
%  * set_weights(W)
%  * mul_weights(K)

edit_probs(goal:Head, Method, pdcg(In1,In2), pdcg(Out1,In2)) :-
	maplist(rule_edit(Head,Method),In1,Out1).

edit_probs(rule:Head, Method, pdcg(In1,In2), pdcg(In1,Out2)) :-
	maplist(rule_edit(Head,Method),In2,Out2).



% These depend on the chosen distribution representation

print(H,S,S) :- unzipweights(S,W,_), print(H:W), nl. % writeln(H:W)
print_head(H,S,S) :- unzipweights(S,W,_), length(W,N), format('~w:<~d records>\n',[H,N]).
print_all(H,S,S) :- format('\n---head: ~w\n',[H]), print_list(S).
get_weights(H,W,H,S,S) :- unzipweights(S,W,_).
set_weights(W,_,S1,S2) :- zipweights(W,S1,S2).
mul_weights(K,_,S1,S2) :- maplist(mul,K,S1,S2).

% if heads unify - apply method, otherwise, do nothing
rule_edit(Head,Meth,rule(H,Solns),rule(H,Solns1)) :- 
	(	unifiable(Head,H,_) -> call(Meth,H,Solns,Solns1)
	;	Solns1=Solns
	).
	

rule_product(rule(Head,Solns0),rule(Head,Solns1),rule(Head,Solns2)) :-
	unzipweights(Solns0,W0,_),
	maplist(mul,W0,Solns1,Solns2).

rule_cool(DT,rule(Head,Solns),rule(Head,Solns1)) :-
	unzipweights(Solns,W0,_),
	maplist(power(DT),W0,W),
	zipweights(W,Solns,Solns1).


% sample new distributions from Dirichlet
rule_resample(Method,rule(Head,Solns0),rule(Head,Solns1),rule(Head,Solns4)) :-
	unzipweights(Solns0,W0,V0,N),
	unzipweights(Solns1,W1,N),
	call(Method,V0,W0,W1,Params),
	sample(dirichlet(N,Params),W2),
	zipweights(W2,Solns1,Solns2),
	sort(Solns2,Solns3),
	reverse(Solns3,Solns4).

rule_resample(Method,rule(Head,Solns),rule(Head,Solns3)) :-
	unzipweights(Solns,W0,V0,N),
	call(Method,V0,W0,Params),
	sample(dirichlet(N,Params),W),
	zipweights(W,Solns,Solns1),
	msort(Solns1,Solns2),
	reverse(Solns2,Solns3).



dirichlet(Alpha,V0,_,A0) :- maplist(mult(Alpha),V0,A0).
specialise(Mult,_,W0,A0) :- sumlist(W0,T), maplist(mult(Mult/T),W0,A0).

diffuse(Mult,Rate,BG, V0, W0, A0) :- 
	maplist(mult(BG),V0,Z0),
	sumlist(W0,T), 
	maplist(mult(Mult/T),W0,A1),
	maplist(diff,A1,Z0,DA),
	pnorm(2,DA,NormDA),
	K is 1/(1+Rate*NormDA),
	maplist(linterp_d(K),Z0,DA,A0).

diffuse(Rate,BG, V0, Z1, Z) :- 
	maplist(mult(BG),V0,Z0),
	K is 1/Rate,
	maplist(linterp_d(K),Z0,Z1,Z).


% diffuse towards a particular background model
diffuse_to(Rate,Mult,BG,_,Z1,Z) :- 
	K is 1/Rate,
	sumlist(BG,T),
	maplist(mult(Mult/T),BG,Z0),
	maplist(linterp_d(K),Z0,Z1,Z).

power(DT,X,Y) :- Y is X^DT.
pnorm(2,X,N) :- sumsquares(X,SSX), N is sqrt(SSX).
pnorm(1,X,N) :- sumlist(X,N).
sumsquares([],0).
sumsquares([X|Y],T) :- sumsquares(Y,T1), T is (X*X)+T1.
linterp_d(K,Z0,D,Z) :- Z is Z0+K*D.
diff(X,Y,Z) :- Z is X-Y.
mult(K,X,Y) :- Y is K*X.

zipweights([],[],[]).
zipweights([W|WX],[_-R1|RX],[W-R1|SX]) :- zipweights(WX,RX,SX).


unzipweights([],[],0).
unzipweights([W-_|SX],[W|WX],N) :- unzipweights(SX,WX,M), succ(M,N).

unzipweights([],[],[],0).

unzipweights([W-soln(_,V)|SX],[W|WX],[V|VX],N) :- 
	unzipweights(SX,WX,VX,M), succ(M,N).

unzipweights([W-clause(_,_,_,_,V)|SX],[W|WX],[V|VX],N) :- 
	unzipweights(SX,WX,VX,M), succ(M,N).

sumweights([],0).
sumweights([W-_|XX],T) :- sumweights(XX,T0), T is W+T0.


mul(K,X-Z,Y-Z) :- Y is X*K.



%% tron is det.
%% tron( +Flags) is det.
%
%  Control execution tracing. Flags is a term like (Pre/Post/Match),
%  where each value is 0 or 1. The components have the following
%  meanings:
%  * Pre   
%    enables tracing of rule entry.
%  * Post  
%    enables tracing of rule exit.
%  * Match  
%    enables message when no matches are found for a rule.
%    Equivalent to tron(1/1/1).

tron :- tron(1/1/1).
tron(F) :-
	retractall(rtrace(_,_)),
	assert(rtrace(P,T) :- trace_write(P,F,T)).

%% troff is det.
%
%  Switches off all tracing, equivalent to tron(0/0/0).

troff :-
	retractall(rtrace(_,_)),
	assert(rtrace(_,_) :- true).

trace_write(pre,1/_/_,T:H) :-  bt_call(writeln(call->T:H),writeln(fail->T:H)).
trace_write(post,_/1/_,T:H) :- bt_call(writeln(exit->T:H),writeln(redo->T:H)).
trace_write(pre,0/_/_,_).
trace_write(post,_/0/_,_).

trace_write(match_check(dist(_,[_|_])),_,_).
trace_write(match_check(dist(_,[])),_/_/0,_). 
trace_write(match_check(dist(_,[])),_/_/1,T:G) :- 
	format('*** no matches for ~w:~w\n',[T,G]), fail.

bound(_=Value) :- nonvar(Value).



% some useful rules.. 
%
with(S,G) ---> iso((set(S),G)).
iso(G)    ---> get(T), G, set(T).

rep(0,_) ---> [].
rep(N,G) ---> 
	(	{var(N)} 
	-> {copy_term(G,G1)}, G1, rep(M,G), {succ(M,N)}
	;	(	{N=0} -> []
		;	{succ(M,N)}, {copy_term(G,G1)}, G1, rep(M,G)
		)
	).

%user:portray(pdcg(A,B)) :- write_term(pdcg(A,B),[max_depth(5)]).
user:portray(pdcg(GS,RS)) :- 
	length(RS,N1), length(GS,N2), 
	format('pdcg<~w goals, ~w rules>',[N2,N1]).

:- troff.
