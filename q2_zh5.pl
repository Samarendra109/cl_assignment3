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
lan(zh).
question(q2).

bot sub [cat, sem, list, logic, gap_struct, agr].
    cat sub [gappable, agreeable, dou] intro [logic:logic, qstore:list].
        gappable sub [verbal, n, np, n_np_vp] intro [gap:gap_struct, sem:sem].
            verbal sub [vp, s, v] intro [subcat:list].

        agreeable sub [cl_agreeable, q_agreeable, n_np_vp] intro [agr:agr].
            cl_agreeable sub [cl, n] intro [agr:cl_agr].
            q_agreeable sub [np_vp, q] intro [agr:quant].

        n_np_vp sub [n, np_vp].
            np_vp sub [np, vp].

        n intro [cl:cl].

    agr sub [cl_agr, quant].
        cl_agr sub [ge, zhong].

    gap_struct sub [none, np].

    sem sub [hacker, language, speak].

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
% 每: the universal quantifier
mei ---> (q,
    logic: @lambda(F, 
                @lambda(P, 
                    @forall(Y, 
                        @apply(F, [Y]),
                        @apply(P, [Y])))),
    qstore:[],
    agr:forall).

% 一: the existential quantifier
yi ---> (q,
    logic: @lambda(F, 
                @lambda(P, 
                    @exists(Y, 
                        @apply(F, [Y]),
                        @apply(P, [Y])))),
    qstore:[],
    agr:exists).

% 个: the classifier for hackers
ge ---> (cl, agr:ge).
% 种: the classifier for languages
zhong ---> (cl, agr:zhong).

% 都: the distributive operator
dou ---> dou.

% 语言: language
yuyan ---> (n,
    agr:zhong,
    logic: @lambda(X, @apply(Language, [X])),
    qstore:[],
    sem:(language, Language)).

% 黑客: hacker
heike ---> (n,
    agr:ge,
    logic: @lambda(X, @apply(Hacker, [X])),
    qstore:[],
    sem:(hacker, Hacker)).

% 会说: speak
huishuo ---> (v,
    logic: @lambda(Q, 
                @lambda(Z, 
                    @apply(Q, [
                        @lambda(X, @apply(Speak, [Z, X]))
                    ]))),
    qstore:[],
    subcat:[], % the subcat list should not be empty
    sem:(speak, Speak)).

% Phrase structure rules (incomplete)
np rule
    (np, sem:N_sem, logic:NP_logic, qstore:NP_qstore, agr:(quant, Q_agr), gap:none) ===>
    cat> (q, logic:Q_logic, agr:Q_agr),
    cat> (cl, agr:(cl_agr, CL_agr)),
    sem_head> (n, sem:N_sem, logic:N_logic, qstore:N_qstore, agr:CL_agr),
    goal> apply_normalize_and_qaction(
        Q_logic, N_logic, N_qstore, NP_logic, NP_qstore
    ).

vp rule
    (vp, sem:V_sem, logic: VP_logic, qstore: NP_qstore, agr:exists, subcat: [NP], gap:Gap) ===>
    sem_head> (v, sem:V_sem, logic:V_logic),
    cat> (np, logic:NP_logic, qstore: NP_qstore, gap:Gap, NP),
    goal> check_gap_and_normalize(V_logic, NP, VP_logic).

dou rule
    (vp, sem:VP_sem, logic: VP_logic, qstore: VP_qstore, agr:forall, subcat: VP_subcat) ===>
    cat> (dou),
    sem_head> (vp, sem:VP_sem, logic: VP_logic, qstore: VP_qstore, agr:exists, subcat: VP_subcat).

s rule
    (s, sem:VP_sem, logic: S_logic, qstore: S_qstore, gap:(none, None)) ===>
    cat> (np, logic:NP_logic, qstore: e_list, agr:(quant, NP_agr), gap:None, NP),
    sem_head> (vp, sem:VP_sem, logic:VP_logic, qstore: VP_qstore, agr:NP_agr, gap:None, subcat:VP_subcat),
    goal> apply_normalize_and_retrieve(NP, NP_logic, VP_logic, VP_qstore, S_logic, S_qstore).

s_gap rule
    (s, sem:VP_sem, logic: S_logic, qstore: S_qstore, gap:(none, None)) ===>
    cat> (np, logic:NP_Obj_logic, qstore: NP_Obj_qstore, gap:None, NP_Obj),
    cat> (np, logic:NP_Sub_logic, qstore: e_list, agr:(forall, Forall), gap:None, NP),
    sem_head> (vp, sem:VP_sem, logic:VP_logic, qstore: VP_qstore, agr:Forall, gap:Gap, VP),
    goal> resolve_gap_and_normalize(NP, NP_Sub_logic, VP, NP_Obj, S_logic, S_qstore).

% The empty category
empty (np, sem:Sem, logic:Logic, qstore:QStore, agr:Agr,
    gap:(sem:Sem, logic:Logic, qstore:QStore, agr:Agr, gap:none)).

% Macros
lambda(X, Body) macro (lambda, bind:X, body:Body).
forall(X, Restr, Body) macro (forall, bind:X, body:(imply, lhs:Restr, rhs:Body)).
exists(X, Restr, Body) macro (exists, bind:X, body:(and, lhs:Restr, rhs:Body)).
apply(F, Args) macro (app, f:F, args:Args).

% extra helper goals
apply_normalize_and_qaction(LogicFunc, LogicArg, QStore, NewLogic, NewQStore) if
    beta_normalize(@apply(LogicFunc, [LogicArg]), Norm_logic),
    qaction(Norm_logic, QStore, NewLogic, NewQStore).

is_ambiguous((np, agr:NP1_agr), [(l:body:NP2_agr)]) if
    bn_quant(NP1_agr, forall),
    bn_quant(NP2_agr, exists).

apply_normalize_and_retrieve(NP1, LogicFunc, LogicArg, QStore, NewLogic, NewQStore) if
    is_not_empty(QStore),
    is_ambiguous(NP1, QStore),
    beta_normalize(@apply(LogicFunc, [LogicArg]), Norm_logic),
    retrieve(QStore, Norm_logic, NewQStore, NewLogic).

apply_normalize_and_retrieve(NP1, LogicFunc, LogicArg, QStore, Norm_logic, QStore) if
    is_empty(QStore),
    beta_normalize(@apply(LogicFunc, [LogicArg]), Norm_logic).

is_not_gap(none) if true.
is_gap(np) if true.

check_gap_and_normalize(V_logic, (np, logic: NP_logic, gap:Gap), VP_logic) if
    is_not_gap(Gap),
    beta_normalize(@apply(V_logic, [NP_logic]), VP_logic).

check_gap_and_normalize(V_logic, (np, logic: NP_logic, gap:Gap), V_logic) if
    is_gap(Gap).

is_not_empty([_|_]) if true.

resolve_gap_and_normalize(
        NP,
        NP_Sub_logic, 
        (vp, logic: VP_logic, gap:Gap), 
        (np, logic:NP_Obj_logic, qstore: NP_Obj_qstore, NP_obj), 
        S_logic, S_qstore
    ) if
    is_gap(Gap),
    beta_normalize(@apply(VP_logic, [NP_Obj_logic]), VP_Obj_logic),
    beta_normalize(@apply(NP_Sub_logic, [VP_Obj_logic]), Norm_logic),
    is_not_empty(NP_Obj_qstore),
    retrieve(NP_Obj_qstore, Norm_logic, S_qstore, S_logic).

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
prect_test :- prec([yi,ge,heike,huishuo,mei,zhong,yuyan]).
translate_test :- translate([yi,ge,heike,huishuo,mei,zhong,yuyan]).
