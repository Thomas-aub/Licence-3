Require Import Utf8.

(***************************** LIFLC - TP1*************************************)
(********************** premières preuves en coq ******************************)
(******************************************************************************)

(*
  L'objectif de LIFLC-TP1 est de prendre en main la partie preuve de Coq à 
  travers quelques exercices sur la logique propositionnelle.

  Alors que dans LIFLF-TP1 on avait écrit quelques types et programmes 
  fonctionnels simples (dans Coq on dira qu'ils sont dans *Set* ) comme les
  entiers de Peano et l'arithmétique de base, ici, on va écrire quelques
  *preuves* simples (qui sont dans *Prop* ).

  Dans les TP qui suivront, on fera la jonction des objets de *Set* et de *Prop*
  en prouvant des propriétés des programmes.

  Documentations:

  * [Documentations officielle de Coq](https://coq.inria.fr/refman/)
  * [Petit guide de survie en Coq](http://lim.univ-reunion.fr/staff/fred/Enseignement/IntroCoq/Exos-Coq/Petit-guide-de-survie-en-Coq.html)
  * [Cheat sheet](http://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf)

*)

Section LIFLC_TP1.

(******************************************************************************)
(* Préliminares *)
(******************************************************************************)

(* Charger le présent  fichier  dans CoqIDE ou Proof General (mode emacs).
Exécuter pas à pas la preuve du théorème `application` (jusqu'au 1er `Qed`).
Chaque _instruction_ Coq dans la preuve est une _tactique_.
Ces _instructions_ sont à mettre en parallèle des règles du système de déduction naturelle.

Ici on utilise les tactiques `intro`, `apply` et `exact`. 
Les deux dernières prennent un argument indiquant sur quelle hypothèse travailler. 
On pourra avantageusement remplacer `exact H` par `assumption` qui cherchera
automatiquement une hypothèse `H` qui terminera le but courant.

Il faut bien faire attention à l'évolution de la partie de texte à droite en haut.
Elle contient les hypothèses connues (représentées à gauche du $\vdash$ dans les séquents)
au dessus du trait et ce qu'on veut démontrer (représenté à droite du $\vdash$
dans les séquents) en dessous et qu'on appelle le _but_.

Si une dérivation contient plusieurs branches, les formules à démontrer sont
ajoutées sous de nouveaux traits et sont appellées _sous-buts_.

Essayer de faire correspondre chaque tactique utilisée à une règle de la déduction naturelle. 
Il est possible de s'aider du [guide de survie] pour cela.
Voir le mémo [ReglesDeducNat.pdf](./ReglesDeducNat.pdf) pour un réponse à cette question.
 *)
 
(* On introduit les variables avec lesquelles on va travailler par la suite *)
Hypothesis P Q R: Prop.

(* La preuve vue en cours, à dérouler pas à pas *)
Theorem application: P -> ((P -> Q) -> Q).
Proof.
  intro HP.
  intro HPQ.
  apply HPQ.
  exact HP. (* ou assumption *)
Qed.

(******************************************************************************)
(* Exercice 1 *)
(******************************************************************************)

(* Compléter les preuves du théorème `exercice_1_a` avec les mêmes tactiques que
la preuve de `application`. Quand Coq valide la preuve (c'est vert dans CoqIDE),
remplacer `Admitted.` par `Qed.`.
 *)

(* Compléter la preuve de l'exercice 1a *)
Theorem exercice_1_a: (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  Admitted.


(* Pour l'`exercice_1b`, on utilisera, en plus des tactiques précédentes,
la tactique `destruct` qui permet d'éliminer un type inductif en hypothèse,
ici une conjonction. 

En effet, la conjonction dans Coq n'est qu'un type inductif particulier dans Prop.
Pour construire `A /\ B` (qui est juste une notation pour `and A B`), il faut
donner à Coq deux objets une preuve de `À` et une preuve de `B`. 

C'est ce qu'on voit quand on exécute `Check (and P Q).`, `Print and.` et `Check conj.`.
Ces définitions primitives de Coq sont dans le fichier.
https://github.com/coq/coq/blob/master/theories/Init/Logic.v

 *)
Check (and P Q).
Print and.
Check conj.

(* Une variante de la précédente avec /\ dans les hypothèses *)
Theorem exercice_1b: (P -> Q) /\ (Q -> R) -> (P -> R).
Proof.
  Admitted.


(* Pour la preuve de `ex_falso_quodlibet`, il faut comprendre que `False` est un
type inductif sans constructeur qui n'a donc ainsi aucun élément.
En l'éliminant avec `destruct`, on termine la preuve car qu'il n'y a plus rien
à prouver quand on a un preuve de `False`.
 *)

Theorem ex_falso_quodlibet : False ->  P.
Proof.
  Admitted.

(* Pour traiter la disjonction dans la preuve de `exercice_1_c`, on utilisera
`destruct` sur l'hypothèse, ce qui génèrera deux sous-buts : un pour chaque
branche de la disjonction notée `\/`.
En effet, pour prouver que `A \/ B |- C`, il suffit de montrer `A |- C` et `B |- C`. *)

(* Quant à la disjonction dans le but, en Coq, il faut dire quelle branche on
souhaite prouver avec les tactiques `left` et `right`.
 *)


(* Compléter la preuve de l'exercice 1c *)
Theorem exercice_1_c: (P \/ Q) -> (Q \/ P).
Proof.
  Admitted.

(* Les tactiques `left` et `right` ne sont rien d'autres que des raccourcis pour
'utilise le premier constructeur' pour la tactique `left` et pour
'utilise le second constructeur' pour la tactique `right`.
Sur le cas d'espèce, on a le même effet avec `apply or_introl.` et
`apply or_introl.`
 *)
 
Print or.


(**********************************************************************)
(* Exercice 2 *)

(* Pour faciliter le suivi de la preuve, il est possible de d'indenter et de
mettre le _focus_ sur le sous-but courant avec des _items_ `*`, `+ `ou `-`.
Voir la preuve `exemple_avec_items`.
 
Pour la preuve du théorème `exemple_avec_items`, on utilise la tactique `split`
qui génère un sous but pour chaque membre de la conjonction, c'est-à-dire ici
pour chacun des deux paramètres du constructeur `conj`.
On obtient la même chose avec `apply conj`.
*)

Theorem exemple_avec_items: P /\ Q -> Q /\ P.
Proof.
  intro HPQ.
  split.
  * destruct HPQ.
    assumption.
  * destruct HPQ.
    assumption.
Qed.

(* Si les preuves pour deux sous-buts générés sont les mêmes, on peut en séparer
les étapes par `;` au lieu de `.` afin de les réutiliser dans les sous cas.
Dérouler pas à pas la preuve de `exemple_avec_items_court` pour en comprendre
le fonctionnement. *)

Theorem exemple_avec_items_court : P /\ Q -> Q /\ P.
Proof.
  intro HPQ.
  split; destruct HPQ; assumption.
Qed.

(* Quand on utilise la tactique `destruct H` on peut préciser le nom des
hypothèses générées avec la syntaxe `destruct H as [Ha Hb]`.
Les curieux iront voir la documentation officielle
https://coq.inria.fr/refman/proof-engine/tactics.html?highlight=destruct#coq:tacn.destruct
 *)

(* Faire les preuves des théorèmes `exercice_2_a` et `exercice_2_b`.
Pour `exercice_2_b` le symbole `<->` ("iff") n'est qu'une définition pour
la conjonction des deux implications
"Definition iff (A B:Prop) := (A -> B) /\ (B -> A)."
Il donc est possible d'utiliser la tactique `split`.
*)

Print iff.

(* Utiliser la tactique split pour traiter un /\ à démontrer. *)
Theorem exercice_2_a: ((P -> Q -> R) -> (P /\ Q -> R)) /\ ((P /\ Q -> R) -> (P -> Q -> R)) .
Proof.
  Admitted.

Theorem exercice_2_b: (P -> Q) /\ (P -> R) <-> (P -> Q /\ R).
Proof.
  Admitted.

(* Utiliser la tactique `unfold not` pour remplacer la définition de la négation
`¬ X` par `X → False` dans la preuve de `exercice_2_c`.
Avec un peu d'habitude, comme on sait que `¬ X` n'est qu'un jeu d'écriture pour
`X → False`, on utilise directement les tactiques `intros` et `apply` sans
utiliser `unfold not` explicitement (Coq sait le faire pour nous).
 *)

(* une 'demie-loi' de De Morgan *)
Theorem exercice_2_c: (~P \/ ~Q) -> ~(P /\ Q).
Proof.
  Admitted.
  

(* une loi de De Morgan *)
Theorem exercice_2_d: ~(P \/ Q) <-> (~P /\ ~Q).
Proof.
  Admitted.



(**********************************************************************)
(* Exercice 3 *)

(* Les théorèmes suivants utilisent le tiers exclus, qui doit être soit être
supposé vrai en Coq. En effet, le paradigme logique sous-jacent à Coq est
_intuitionniste_ (et non _classique_ comme dans _logique classique_), il ne
permet pas de _prouver_ le tiers exclus sans hypothèse supplémentaire.

C'est la raison pour laquelle on introduit "Context Tiers_exclus: forall X: Prop, X \/ ~X."
qui stipule que toute proposition est soit vraie soit fausse : on ajoute le
tiers exclu au contexte. 

Contempler l'usage de `Tiers_exclus`` dans les preuves des `tiers_exclu_pour_P` et `tiers_exclu_pour_Q`.
*)


Context (Tiers_exclus: forall X: Prop, X \/ ~X).

Lemma tiers_exclu_pour_P : P \/ ~P.
(* si c'est vrai pour tout X, alors c'est aussi le cas pour P *)
exact (Tiers_exclus P).
Qed.

Lemma tiers_exclu_pour_Q : (P -> Q) /\ (~P -> Q) -> Q.
Proof.
intros H; destruct H as [H1 H2].
destruct (Tiers_exclus P).
 - apply H1; assumption.
 - apply H2; assumption.
Qed.

(* Prouver les théorèmes `exercice_3_a` (en utilisant bien sûr `exercice_2_c`) et `exercice_3_b`.  *)
Theorem exercice_3_a:  ~(P /\ Q) <-> ~P \/ ~Q.
Proof.
  Admitted.

Theorem exercice_3_b: ((P -> Q) -> P) -> P.
Proof.
  Admitted.

(* Prouver le théorème `exercice_3_b`. Contempler l'asymétrie :
   un seul des sens de l'équivalence utilise le tiers exclu.
*)

Theorem exercice_3_c: (~~P <-> P).
Proof.
  Admitted.

(* Plus généralement, les curieux iront apprécié les 'demies équivalences'
valides en logique intuitionniste, comme l'exemple de l'implication matérielle
 https://en.wikipedia.org/wiki/Intuitionistic_logic#Non-interdefinability_of_operators
 *)

Theorem exercice_3_d: (~P \/ Q) <-> (P -> Q).
Proof.
  Admitted.


End LIFLC_TP1.















