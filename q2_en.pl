% Student name: NAME
% Student number: NUMBER
% UTORid: ID

% This code is provided solely for the personal and private use of students
% taking the CSC485H/2501H course at the University of Toronto. Copying for
% purposes other than this use is expressly prohibited. All forms of
% distribution of this code, including but not limited to public repositories on
% GitHub, GitLab, Bitbucket, or any other online platform, whether as given or
% with any changes, are expressly prohibited.

% Authors: Jingcheng Niu and Gerald Penn

% All of the files in this directory and all subdirectories are:
% Copyright c 2022 University of Toronto

:- ensure_loaded(csc485).
:- ale_flag(pscompiling, _, parse_and_gen).
lan(en).
question(q2).

bot sub [cat, sem, list, logic, func, qs, gap_struct, e].
    cat sub [q, det, gappable, has_sem] intro [logic:logic, qstore:list].
        has_sem sub [n, gappable] intro [sem:sem].
            gappable sub [np, verbal] intro [gap:gap_struct].
                verbal sub [v, vp, s] intro [subcat:list].

    e intro [logic:logic].

    gap_struct sub [none, np].

    sem sub [hacker, language, speak, f, g, h].

    list sub [e_list, ne_list].
        ne_list intro [hd:bot, tl:list].

    logic sub [free, scopal].
        scopal sub [lambda, quant] intro [bind:logic, body:logic].
            quant sub [exists, forall] intro [bind:qvar].
        free sub [op, app, qvar].
            op sub [and, imply] intro [lhs:logic, rhs:logic].
            app intro [f:func, args:list].
    func sub [lambda, sem].

    qs intro [l:logic, x:logic].

% Lexical entries (incomplete)
every ---> (q,
    logic: @lambda(F, @lambda(P, @forall(X, F, P)))
    % qstore:[]
    ).

a ---> (q,
    logic: @lambda(F, @lambda(P, @exists(X, F, P)))
    % qstore:[]
    ).

language ---> (n,
    logic: @lambda(X, @apply(Language, [X])),
    % qstore:[],
    sem:(language, Language)).

hacker ---> (n,
    logic: @lambda(X, @apply(Hacker, [X])),
    % qstore:[],
    sem:(hacker, Hacker)).

speaks ---> (v,
    logic: @lambda(Q, 
                @lambda(Z, 
                    @apply(Q, [
                        @lambda(X, @apply(Speak, [Z,X]))
                    ]))),
    % qstore:[],
    subcat:[], % the subcat list should not be empty
    sem:(speak, Speak)).

% Î»x. f(x)
b ---> (e, logic: @lambda(X, @apply(f, [X]))).
% Î»F. âˆ€x. F(x)
c ---> (e, logic: @lambda(F, (forall, bind: X, body: @apply(F, [X])))).
% Î»F. âˆ€x. F(x) => F(x)
d ---> (e, logic: @lambda(
            F,
            @forall(X,
                @apply(F, [X]),
                @apply(F, [X])))).

beta rule
(e, logic:LF3) ===>
cat> (e, logic:LF1),
cat> (e, logic:LF2),
goal> beta_normalize(@apply(LF1, [LF2]), LF3).

% Phrase structure rules (incomplete)
np rule
    (np, logic: NP_logic) ===>
    cat> (q, logic: Q_logic),
    sem_head> (n, logic: N_logic),
    goal> beta_normalize(@apply(Q_logic, [N_logic]), NP_logic).

vp rule
    (vp, logic: VP_logic) ===>
    sem_head> (v, logic: V_logic),
    cat> (np, logic: NP_logic),
    goal> beta_normalize(@apply(V_logic, [NP_logic]), VP_logic).

s rule
    (s, logic: S_logic) ===>
    cat> (np, logic: NP_logic),
    sem_head> (vp, logic: VP_logic),
    goal> beta_normalize(@apply(NP_logic, [VP_logic]), S_logic).

s_gap rule
    (s) ===>
    cat> (Gap),
    cat> (np),
    sem_head> (vp).

% The empty category:
empty (np, sem:Sem, logic:Logic, qstore:QStore,
    gap:(sem:Sem, logic:Logic, qstore:QStore, gap:none)).

% Macros
lambda(X, Body) macro (lambda, bind:X, body:Body).
forall(X, Restr, Body) macro (forall, bind:X, body:(imply, lhs:Restr, rhs:Body)).
exists(X, Restr, Body) macro (exists, bind:X, body:(and, lhs:Restr, rhs:Body)).
apply(F, Args) macro (app, f:F, args:Args).

% Helper goals
append([],Xs,Xs) if true.
append([H|T1],L2,[H|T2]) if append(T1,L2,T2).
is_empty([]) if true.

% Beta normalization goals
beta_normalize((lambda,Lambda),Lambda) if !,true.
beta_normalize((Input,bind:Bind,body:Body),(Output,bind:Bind,body:BetaBody)) if
    bn_quant(Input,Output),
    beta_normalize(Body,BetaBody).
beta_normalize((Input,lhs:LHS,rhs:RHS),(Output,lhs:BetaLHS,rhs:BetaRHS)) if
    bn_op(Input,Output),
    beta_normalize(LHS,BetaLHS),
    beta_normalize(RHS,BetaRHS).
beta_normalize(@apply(@lambda(X,Body),[X]),Beta) if 
    !,beta_normalize(Body,Beta).
beta_normalize((app,Apply),Apply) if true.

bn_quant(exists,exists) if true.
bn_quant(forall,forall) if true.
bn_op(and,and) if true.
bn_op(imply,imply) if true.

% Quantifier actions
store(Logic, QStore, @lambda(F, @apply(F,[X])), 
                     [(l:Logic, x:X)|QStore]) if true.

qaction(Logic, QStore, Logic, QStore) if true.
qaction(Logic, QStore, NewLogic, NewQStore) if
    store(Logic, QStore, NewLogic, NewQStore).

retrieve((Empty, []), Logic, Empty, Logic) if true.
retrieve([(l:QLogic, x:X)|T], Logic, T, NewLogic) if 
    beta_normalize(@apply(QLogic, [@lambda(X, Logic)]), NewLogic).

% Specifying the semantics for generation.
semantics sem1.
sem1(logic:S, S) if true.
sem1(sem:S, S) if true.

% Some examples
% You should write more
prect_test :- prec([a,hacker,speaks,every,language]).
translate_test :- translate([a,hacker,speaks,every,language]).
