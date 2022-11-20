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

:- ale_flag(pscompiling, _, parse_and_gen).
:- ensure_loaded(csc485).
lan(zh).
question(q1).

bot sub [cat, sem, agr, cl_types, list].
    sem sub [n_sem, v_sem].
        n_sem sub [mouse, sheep, linguist] intro [count:count].
        v_sem sub [see, chase] intro [subj:sem, obj:sem].

    cl_types sub [ge, wei, zhi, tou].

    cat sub [nominal, verbal] intro [agr:agr, sem:sem].
        nominal sub [n, np, clp, num, cl] intro [sem:n_sem].
        verbal sub [v, vp, s] intro [sem:v_sem, subcat:list].

    % Define your agreement
    agr intro [cl:cl_types].

    count sub [one, two, three].

    list sub [e_list, ne_list].
        ne_list intro [hd:bot, tl:list].

% Specifying the semantics for generation.
semantics sem1.
sem1(sem:S, S) if true.

% Define your Lexical items
yi ---> (num, sem:(n_sem, count:one)).
liang ---> (num, sem:(n_sem, count:two)).
san ---> (num, sem:(n_sem, count:three)).
laoshu ---> (n, agr:cl:zhi, sem:mouse).
yang ---> (n, agr:cl:tou, sem:sheep).
yuyanxuejia ---> (n, agr:cl:ge, sem:linguist).
yuyanxuejia ---> (n, agr:cl:wei, sem:linguist).
kanjian ---> (v, sem:see).
zhui ---> (v, sem:chase).
ge ---> ge.
wei ---> wei.
zhi ---> zhi.
tou ---> tou.

% Define your Rules
snpvp rule
(s, sem:(V_sem, subj:NP, obj:NP_o)) ===> cat> (np, NP),
                                         cat> (vp, sem:(V_sem, obj:NP_o)).

%vpvnp rule
%(vp, sem:(V_sem, obj:NP)) ===> cat> (v, sem:V_sem),
%                               cat> (np, NP).

%vpvnp rule
%(vp, sem:(V_sem, obj:NP)) ===> cat> (v, sem:V_sem),
%                               cat> (np, NP).

vpvnp rule
(vp, VP_sem) ===> cat> (v, sem:V_sem),
                      cat> (np, NP),
                      goal> sem1(VP_sem, (V_sem, obj:NP)).

vpvn rule
(vp, sem:obj:NP) ===> cat> v,
                      cat> (np, NP).

npclpn rule
(np, agr:cl:Cl_type, sem:(N_sem, count:Count)) ===> cat> (clp, agr:cl:Cl_type, sem:count:Count),
                                           cat> (n, agr:cl:Cl_type, sem:N_sem).

clpnumcl rule
(clp, agr:cl:Cl_type, sem:count:Count) ===> cat> (num, sem:count:Count),
                                            cat> (cl_types, Cl_type).


