Require Import Utf8.

(***************************** LIFLC - TP2*************************************)
(******************** preuves par induction en Coq ****************************)
(******************************************************************************)

(* 
   L'objectif de ce TP est de poursuivre la partie 'preuve' de Coq avec
   des preuves par induction sur les types inductifs (entiers, listes) tels
   qu'utilisés dans LIFLF-TP1
 
   Documentations : 
       * #<a href="https://coq.inria.fr/distrib/current/refman/Reference-Manual018.html">CoqIDE</a>#
       * #<a href="http://lim.univ-reunion.fr/staff/fred/Enseignement/IntroCoq/Exos-Coq/Petit-guide-de-survie-en-Coq.html">Petit guide de survie en Coq</a>#
       * #<a href="http://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf">Cheat sheet</a>#
       * #<a href="https://www.lri.fr/~paulin/MathInfo2/coq-survey.pdf">Coq Survey</a> (Guide coq de Christine Paulin-Mohring)</a>#

   Charger le fichier LIFLC-TP2.v dans CoqIDE ou ProofGeneral.
*)

Section my_list.

(******************************************************************************)
(* STRUCTURE DE BASE DES LISTES (FINIES) D'ENTIERS                            *)
(******************************************************************************)

(* Comme exemple de type inductif, les entiers (dits 'de Peano') ont été définis
   dans LIFLF-TP1 comme suit *)

Inductive entiers : Type :=
  | Z : entiers
  | Succ : entiers -> entiers.

(*  Coq fournit un type comparable dans la bibliothèque standard, c'est le type "nat"
   https://coq.inria.fr/library/Coq.Init.Datatypes.html

   Inductive nat : Set :=
    | O : nat
    | S : nat -> nat.  *)


(* Reprenons l'exemple de type inductif "nlist" des listes d'entiers naturels
   qui constituait la partie 2 du TP LIFLF-TP1.
 *)

Inductive nlist : Set :=
  | nnil : nlist                   (* nnil est la liste vide *)
  | ncons : nat -> nlist -> nlist. (* ncons a l est la liste obtenue 
                                  en ajoutant a en tête de l *)

(* 
   En  regardant de  plus près  la définition,  on voit que  les deux 
   constructeurs  de ces listes, "nnil" et "ncons", sont vus par Coq
   comme des  fonctions qui renvoient le type "nlist".

   Le  constructeur "nnil" ne  prend pas d'argument, c'est une constante.
   Le constructeur "ncons" prend deux  arguments : un entier (type "nat")
   et une liste (type "nlist"). Notons que "ncons" est curryfié.
*)

Check nnil.
Check ncons.

(*   Voici quelques listes d'entiers définies grâce au constructeurs de
   liste :

       * la liste vide : nnil
       * la liste à un élément qui contient 3 (fabriquée à partir de 3
         et de la liste vide) : ncons 3 nnil
       * la liste à 2 éléments qui contient 5 et 3 (fabriquée à partir
         5 et de la liste précédente) : ncons 5 (ncons 3 nnil)
 *)

Check 3 : nat.
Check ncons 3 nnil : nlist.
Check ncons 5 (ncons 3 nnil) : nlist.

(* Quelques notations pour faciliter la rédaction et la lecture : *)

Notation "x '::' l" := (ncons x l).
Notation "[ ]" := nnil (format "[ ]").
Notation "[ x ]" := (ncons x nnil).
Notation "[ x ; y ; .. ; z ]" := (ncons x (ncons y .. (ncons z nnil) ..)).


(* Ces notations sont juste... des notations. On s'en convainc en remarquant
   que les listes suivantes "l1" et "l2" sont exactement les mêmes. *)

Definition l1 := ([5;4;3;2;1]).
Definition l2 := (ncons 5 (ncons 4 (ncons 3 (ncons 2 (ncons 1 nnil))))).
Print l1.
Print l2.
Lemma l1_egal_l2 : l1 = l2.
Proof.
reflexivity.
Qed.

(* Les vérifications de type ci-dessus peuvent alors s'écrire : *)
Check [].
Check 3 :: [].
Check 5 :: 3 :: [].
Check [5;4;3;2;1].


(******************************************************************************)
(* PROPRIETES FONDAMENTALES DES CONSTRUCTEURS                                 *)
(******************************************************************************)

(* Comme Coq ne fait AUCUNE hypothèse supplémentaire sur l'égalité entre termes,
   les propriétés suivantes sont vérifiées :

    - les images des constructeurs n'ont pas d'élément en commun ; 
    - les constructeurs sont injectifs (sur chacun de leurs arguments).

   En effet,  si ce  n'était pas  le cas,  alors deux  listes construites
   différement pourraient être égales.
   Les  deux  tactiques  associées   qui  permettent  d'exploiter  ces
   propriétés sont respectivement :
    
    - discriminate
    - injection 
*)

(* NOTA BENE :
   Le mot clé "forall" qui apparaît dans CoqIde écrit "∀" permet d'énoncer
   des propriétés qui doivent être vraies pour toutes les valeurs d'une 
   certaine variable. Par exemple :

      - forall x, x+1 <> 0 se lit 
        "pour tout x, x+1 n'est pas égal à 0"
      - forall x y, x + 1 + y = 1 + x + y se lit 
        "pour tout x et pour tout y, x + 1 + y = 1 + x + y"

  On anticipe ici un peu la partie "premier ordre" de LIFLC mais se
  contenter de la sémantique intuitive de la quantification universelle
  de "pour tous" suffira.
*)

(**********************************************************************)
(* Exercice 1 : prouver "nil_neq_cons" et "cons_injective"            *)
(**********************************************************************)

(* Hint : utiliser les tactiques "discriminate" et "injection" *)
Lemma nil_neq_cons : forall (x:nat) (l:nlist), [] <> x :: l.
Proof.
Admitted.

Lemma cons_injective : forall x xs y ys, (x::xs) = (y::ys) -> (x = y /\ xs = ys).
Proof.
Admitted.


(******************************************************************************)
(* FONCTIONS NON RECURSIVES SUR LES TYPES INDUCTIFS                           *)
(******************************************************************************)

(* En guise de préliminaires, on définit une fonction simple non récursive en 
   utilisant la construction "match" vue en LIFLF-TP1. *)
Definition est_vide (l:nlist) : bool :=
  match l with
  | []       => true
  |  x :: l' => false
  end.

About est_vide.
Compute est_vide [].  (* true *)
Compute est_vide [3].   (* false *)
Compute est_vide [5;3].  (* false *)

(* Ci-dessous, la preuve "est_vide_correcte" qui montre que la fonction renvoie
   "true" si et seulement si son argument est la liste vide.

   La tactique "destruct" permet de faire une analyse par cas sur la construction 
   des listes : un cas pour "nnil" puis un cas pour "ncons".

   On utilise aussi la tactique "simpl" qui permet de réduire un terme, 
   c'est-à-dire de calculer. On écrit "simpl in H" pour calculer dans 
   l'hypothèse "H".
 *)

Lemma est_vide_correcte : forall l, (est_vide l = true) <-> (l = []).
Proof.
  split.
  * (* direction => *)   
    destruct l; intros H.
      - (* cas l = [] *)
        reflexivity.
      - (* cas l = x::l' *)
        (* ici l'hypothèse H est contradictoire *)
        discriminate H.
  * (* direction <= *)   
    destruct l; intros H.
      - (* cas l = [] *)
        simpl.
        reflexivity.
      - (* cas l = x::l' *)
        (* ici l'hypothèse H est contradictoire *)
        discriminate H.
Qed.


(**********************************************************************)
(* Exercice 2 prouver "est_vide_correcte2"                            *)
(**********************************************************************)

(* Hint : quand vos hypothèses sont contradictoires, la tactique
  "exfalso" permet de remplacer le but courant par False en utilisant
  le théorème "ex_falso_quodlibet" de LIFLC-TP1. *)
   
Lemma est_vide_correcte_2 : forall l, (est_vide l = false) <-> (l <> []).
Proof.
Admitted.


(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES ENTIERS                          *)
(******************************************************************************)

(* On va comme premier exemple rappeler la fonction "plus" de LIFLF-TP1. *)

Fixpoint plus (a : entiers) (b : entiers) : entiers :=
  match a with
  | Z => b
  | Succ n => Succ (plus n b)
  end.

(* On montre le lemme suivant par simple calcul de la fonction append avec la tactique "simpl". *)
(* Ici, pas encore besoin d'hypothèse d'induction : ce n'est QUE DU CALCUL. *)
Lemma plus_Z_l : forall a, plus Z a = a.
Proof.
  intros l.
  simpl.
  reflexivity.
Qed. 

(* Par contre, pour le théorème suivant "plus_Z_r", un simple calcul sur le premier argument
   ne suffit pas, il faut utiliser le principe d'induction de Coq sur les "entiers". *)

(* La tactique "rewrite [<-] eq [in H]", où eq est une equation de la forme "x = y"
   et H une hypothèse, permet de récrire un terme x en un terme y (ou y en x avec <-) *)

(* Dérouler la preuve suivante pas à pas pour en comprendre le fonctionnement. *)

Lemma plus_Z_r : forall a, plus a Z = a.
Proof.
induction a  as [ |a' IH]. (* On nomme les variables et l'hypothese d'induction. *)
 - (* cas a = Z, pas de variable et pas d'hypothèse d'induction. *)
   simpl.
   reflexivity.
 - (* cas a = Succ a', a' est une variable et l'hypothèse d'induction est nommée IH. *)
   simpl.
   rewrite -> IH. (* C'est une simple réécriture *)
   reflexivity.
Qed. 


(* Arrêtons-nous un instant : que fait la tactique "induction a" ? La
   même chose que "destruct a" dans le sens où elle analyse la
   construction de "a" sur chacun des cas possibles, "Z" et "Succ a'",
   mais EN AJOUTANT UNE HYPOTHESE D'INDUCTION sur "a'".

   Pour comprendre le principe, supposons une propriété P des entiers :
   - si on peut prouver que (P Z), c'est-à-dire que le 1er entier (0
     moralement) a la propriété P, 
   - et si on peut prouver que si (P a')  alors (P (Succ a')) pour tout "a'" 
   Alors on aura réussi à montrer P sur tous les entiers !
   (L'ensemble des entiers vérifiant la P est stable par les règles de
   construction des entiers, il contient donc les entiers.)

   C'est ce qu'on a étudié dans le LIFLC-TD2 qui portait sur
   l'induction.

   La magie, c'est que Coq est capable AUTOMATIQUEMENT de dériver ce
   principe d'induction à partir de la définition de tout type
   inductif que Coq accepte. Dans le cas présent, le 'récurseur' des
   entiers qui correspond à ce principe est nommé "entiers_ind".  *)

Check entiers_ind.

(* On voit ainsi que le type de "entiers_ind" correspond EXACTEMENT au principe de
   la récurrence usuelle sur les entiers.
    
   "entiers_ind
     : ∀ P : entiers → Prop, P Z → (∀ e : entiers, P e → P (Succ e)) → (∀ e : entiers, P e)"

   C'est un théorème que Coq génère automatiquement et que vous pouvez utiliser dans les preuves.
   Quand on écrit "induction a", finalement, on dit juste à Coq : applique le principe
   d'induction du type de a et fait les "intros" associés. Voir l'exemple ci-dessous
   pour s'en convaincre.
*)

Lemma plus_Z_r' : forall a, plus a Z = a.
Proof.
apply entiers_ind; intros.
 - simpl.
   reflexivity.
 - simpl.
   rewrite -> H. 
   reflexivity.
Qed. 


(**********************************************************************)
(* Exercice 3a  prouver "plus_Succ_r"                                 *)
(**********************************************************************)

(* Hint : par induction. *)
Lemma plus_Succ_r : forall a b, Succ (plus a b) = plus a (Succ b). 
Proof.
Admitted.

(**********************************************************************)
(* Exercice 3b  prouver "plus_commute"                                 *)
(**********************************************************************)

(* Hint : utiliser "plus_Z_r" et "plus_Succ_r" avec la tactique rewrite. *)
Lemma plus_commute : forall a b, plus a b  = plus b a.
Proof.
Admitted.


(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES LISTES                           *)
(******************************************************************************)

(* Le principe d'induction sur les listes est le suivant : supposons une propriété P
   - si on peut prouver que (P []), c'est-à-dire que la liste vide a la propriété P
   - et si on peut prouver que si (P l) alors (P (n::l)) pour tout n
   Alors on aura réussit à montrer P sur toutes les listes.

   C'est ce qu'on a étudié dans le LIFLC-TD2 qui portait sur l'induction.
   Respirez un grand coup et consultez le type de "nlist_ind".
*)

Check nlist_ind.

(* Ce type encapsule le principe d'induction sur les listes. On y retrouve
   les éléments cités juste avant, si on donne  
      * "P" : nlist → Prop : la propriété des listes à prouver
      * "P []" : une preuve que la liste vide a la propiété P (c.-à-d. que [] fait partie des listes qui vérifient P)
      * "∀ (n : nat) (n0 : nlist), P n0 → P (n :: n0)" : la preuve de l'hérédité de P
   Alors, on peut conclure que "∀ n : nlist, P n". *)


(*  On donne ici un élément de réponse de LIFLF-TP1 : la fonction RÉCURSIVE
    de concaténation des listes.
*)

Fixpoint concat (l1 l2 : nlist) : nlist := 
  match l1 with
  | []     => l2
  | x :: l => x::(concat l l2)
  end.

(* On note ++ en notation infixe pour la concaténation. *)
Notation "x '++' y" := (concat x y).



(**********************************************************************)
(* Exercice 4a  prouver "concat_cons" et "concat_nil_l"               *)
(**********************************************************************)

(* Hint : c'est du simple calcul, comme pour "plus_Z_l". *)
Lemma concat_cons : forall (l l':nlist) (a:nat), a :: (l ++ l') = (a :: l) ++ l'.
Proof.
Admitted.

Lemma concat_nil_l : forall l, [] ++  l = l.
Proof.
Admitted.


(**********************************************************************)
(* Exercice 4b  prouver "concat_nil_r"                                *)
(**********************************************************************)

(* Hint : par induction, comme pour "plus_Z_r". *)
Lemma concat_nil_r : forall l, l ++ [] = l.
Proof.
Admitted.

(**********************************************************************)
(* Exercice 4c (optionnel)  prouver "concat_not_comm"                  *)
(**********************************************************************)

(* Montrer un contre-exemple de la commutativité de ++ en utilisant les tactiques vues avant. *)
(* On utilisera la tactique "exists x" où "x" est un témoin avec la propriété recherchée
   quand le but à prouver est de la forme "∃ x. P x". *)
Lemma concat_not_comm : (exists x y, x ++ y <> y ++ x).
Proof.
Admitted.


(******************************************************************************)
(* Exercice 5 : terminer les preuves avec "induction" quand nécessaire        *)
(******************************************************************************)

(* Hint : utiliser rewrite avec l'hypothèse d'induction. *)
Lemma concat_assoc : forall l1 l2 l3, l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
Admitted.

(* NOTA BENE : "concat_assoc", "concat_nil_r" et "concat_nil_r" montrent
   que les listes ont une structure de monoide, avec "concat_not_comm" qui
   précise que ce monoide n'est PAS commutatif *)

(* Hint : utiliser discriminate pour les cas impossibles après induction sur l et sur l' *)
Lemma concat_nil : forall l l':nlist, l ++ l' = [] -> l = [] /\ l' = [].
Proof.
Admitted.


(******************************************************************************)
(* Exercice 6 : fonction de longueur des listes                               *)
(******************************************************************************)

(* Définissez, si vous ne l'avez pas déjà fait dans le LIFLF-TP1 la fonction
   "length" qui compte le nombre d'éléments d'une liste*)

(* TODO : définir cette fonction qui n'est pas censée retourner 0 tout le temps *)
Fixpoint length (l : nlist) : nat := 0.

(* Testez votre fonction... *)
Compute (length []).    (* on attend 0 *)
Compute (length [5;3]). (* on attend 2 *)

(* Démontrez le lemme suivant : *)
Lemma length_of_concat : forall l1 l2, length (l1 ++ l2) = length l1 + length l2.
Proof.
Admitted.


Lemma length_zero_ssi_vide (l : nlist) : length l = 0 <-> l=[].
Proof.
Admitted.


(******************************************************************************)
(* Exercice 6 : fonction de longueur des listes  (POUR ALLER PLUS LOIN)       *)
(******************************************************************************)

(* Si vous êtes joueur, et que vous avez souvenir de la fonction "reduce" vue 
   en LIFAP5, voici un équivalent en Coq *)

Fixpoint foldr (B:Type) (z:B) (f:nat -> B -> B) (l : nlist) : B :=
  match l with
  | []      => z
  | x :: l' => f x (foldr _ z f l')
  end.

(* ... à partir de laquelle on donne la définition suivante *)
Definition length_2 := foldr nat 0 (fun x y => S y).
Check length_2.
Compute (length_2 [5;3]).

(* Prouver le résultat suivant *)
Lemma length_2_is_length : forall l, length_2 l = length l.
Proof.
Admitted.

End my_list.

(******************************************************************************)
(* Exercice 7 : les arbres binaires (POUR ALLER PLUS LOIN)                    *)
(******************************************************************************)

Section BinTree.

(* Éléments dans les noeuds de l'arbre *)
Context {E:Set}.

(* le type inductif *)
Inductive BinTree : Set :=
  | leaf : BinTree 
  | node : BinTree -> E -> BinTree -> BinTree.

(**********************************************************************)
(* On va résoudre la question 3 de l'exo 2 du TD2 de LIFLC            *)
(* Montrer par induction sur Bin E qu'un arbre binaire comportant
   n occurrences de l’arbre vide contient n - 1 éléments non distincts*)
(**********************************************************************)

(* Les deux fonctions qui comptent. *)
(* TODO : définir cette fonction qui n'est pas censée retourner 0 tout le temps. *)
Fixpoint count_leaves (t:BinTree) : nat := 0.

(* TODO : définir cette fonction qui n'est pas censée retourner 0 tout le temps. *)
Fixpoint count_nodes (t:BinTree) : nat := 0.
end.

(* Hint : utiliser "plus_n_Sm" qui est le "plus_Succ_r" de la bibliothèque standard Coq. *)
Lemma count_leaves_nodes : forall (t:BinTree), 1 + (count_nodes t) =  (count_leaves  t).
Proof.
Admitted.

End BinTree.
