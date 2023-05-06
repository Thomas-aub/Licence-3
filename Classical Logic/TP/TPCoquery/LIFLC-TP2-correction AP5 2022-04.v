Require Import Utf8.
Require Import Setoid.

Section my_list.

(**********************************************************************)
(* STRUCTURE DE BASE DES LISTES (FINIES) D'ENTIERS                    *)
(**********************************************************************)

Inductive entiers : Type :=
  | Z : entiers
  | Succ : entiers -> entiers.

Inductive nlist : Set :=
| nnil : nlist                  
| ncons : nat -> nlist -> nlist. 

Infix "::" := ncons.
Notation "[ ]" := nnil (format "[ ]").
Notation "[ x ]" := (ncons x nnil).
Notation "[ x ; y ; .. ; z ]" := (ncons x (ncons y .. (ncons z nnil) ..)).

(******************************************************************************)
(* PROPRIETES FONDAMENTALES DES CONSTRUCTEURS                                 *)
(******************************************************************************)

(* Exercice 1 :prouver "nil_neq_cons" et "cons_injective"      *)
(* Hint : utiliser les tactiques "discriminate" et "injection" *)
Lemma nil_neq_cons : forall (x:nat) (l:nlist), [] <> x :: l.
Proof.
  intros.
  discriminate.
Qed.

Lemma cons_injective : forall x xs y ys, (x::xs) = (y::ys) -> (x = y /\ xs = ys).
Proof.
  intros.
  injection H.
  intros.
  split; assumption.
Qed.


(******************************************************************************)
(* FONCTIONS NON-RECRUSIVES SUR LES TYPES INDUCTIFS                           *)
(******************************************************************************)

(* En guise de préliminaire, on définit une fonction simple non-récursive *)
Definition est_vide (l:nlist) : bool :=
  match l with
  | []       => true
  |  x :: l' => false
  end.

About est_vide.
Compute est_vide [].  (* true *)
Compute est_vide [3].   (* false *)
Compute est_vide [5;3].  (* false *)


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


(* Exercice 2 prouver "est_vide_correcte2" *)
(* Hint : utiliser "simpl in H" pour calculer dans l'hypothèse H *)
(* Hint : quand vos hypothèses sont contradictoires, la tactique
  "exfalso" permet de remplacer le but courant par False en utilisant
  le théorème "ex_falso_quodlibet" de LIFLC-TP1. *)
Lemma est_vide_correcte_2 : forall l, (est_vide l = false) <-> (l <> []).
Proof.
  split.
  * (* direction => *)   
    destruct l; intros H.
      - (* cas l = [] *)
        simpl in H.
        discriminate H.
      - (* cas l = x::l' *)
        discriminate.
  * (* direction <= *)   
    destruct l; intros H.
      - (* cas l = [] *)
        exfalso.
        apply H.
        reflexivity.
      - (* cas l = x::l' *)
        simpl.
        reflexivity.
Restart.
(* là, on va faire une preuve plus élégante dans l'idée, en utilisant "est_vide_correcte"
   mais en pratique, elle est plus pénible qu'autre chose et il faut ajouter 
   "Require Import Setoid." pour pouvoir réécrire des équivalences *)
assert (imp_contra : forall P Q:Prop, (P -> Q) -> (~Q -> ~P)) by tauto.
assert (bool_inv : forall x:bool, x = false <-> ~(x = true)).
 {
    destruct x; split; auto; discriminate || contradiction.
 }

  intros l.
  rewrite bool_inv.
  split; apply imp_contra; apply est_vide_correcte.
Qed.



(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES ENTIER                           *)
(******************************************************************************)

Fixpoint plus (a : entiers) (b : entiers) : entiers :=
  match a with
  | Z => b
  | Succ n => Succ (plus n b)
  end.


Lemma plus_Z_l : forall a, plus Z a = a.
Proof.
  intros l.
  simpl.
  reflexivity.
Qed. 

Lemma plus_Z_r : forall a, plus a Z = a.
Proof.
induction a  as [ |a' IH]. (* on nomme les variables et l'hypothese d'induction *)
 - (* cas a = Z, pas de variable et pas d'hypothèse d'induction *)
   simpl.
   reflexivity.
 - (* cas a = Succ a', a' est une variable et l'hypothèse d'induction est nommée IH *)
   simpl.
   rewrite -> IH. (* c'est une simple réécriture *)
   reflexivity.
Qed. 

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

Lemma plus_Succ_r : forall a b, Succ (plus a b) = plus a (Succ b). 
Proof.
intros a b. induction a as [| a IHa]; simpl; try (rewrite IHa); auto.
Qed.

(**********************************************************************)
(* Exercice 3b  prouver "plus_Succ_r"                                 *)
(**********************************************************************)

Lemma plus_commute : forall a b, plus a b  = plus b a.
Proof.
induction a; intros b.
 - simpl. rewrite (plus_Z_r b). reflexivity.
 - simpl. rewrite (IHa b). rewrite plus_Succ_r. reflexivity.
Qed.



(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION                                          *)
(******************************************************************************)

Fixpoint concat (l1 l2 : nlist) : nlist := 
  match l1 with
  | []     => l2
  | x :: l => x::(concat l l2)
  end.

(* On note ++ en notation infix pour la concatenation *)
Infix "++" := concat.


(**********************************************************************)
(* Exercice 4a  prouver "concat_cons" et  "concat_nil_l"              *)
(**********************************************************************)

Lemma concat_cons : forall (x y:nlist) a, a :: (x ++ y) = (a :: x) ++ y.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma concat_nil_l : forall l, [] ++  l = l.
Proof.
  intros l.
  simpl.
  reflexivity.
Qed.

(**********************************************************************)
(* Exercice 4b  prouver "append_nil_r"                              *)
(**********************************************************************)

Lemma concat_nil_r : forall l, l ++ [] = l.
Proof.
  induction l as [ |n l' IHl]. (* on nomme les variables et l'hypothese d'induction *)
  - (* l = [] : pas de variable et pas d'hypothèse d'induction *)
    simpl.
    reflexivity. 
  - (* l = n::l' : n et l' sont des variables et l'hypothèse d'induction nommée IHl *)
    simpl.
    rewrite -> IHl.
    reflexivity. 
Qed.


(**********************************************************************)
(* Exercice 4c (optionnel)  prouver "append_not_comm"                  *)
(**********************************************************************)

(* Montrer un contre-exemple de la commutativité de ++ en utilisant les tactiques vues avant *)
(* On utilisera la tactique "exists x" où "x" est un témoin avec la propriété recherchée
   quand le but à prouver est de la forme "∃ x. P x" *)
Lemma concat_not_comm : (exists x y, x ++ y <> y ++ x).
Proof.
exists (1::[]).
exists (0::[]).
simpl.
intro H.
injection H.
intros H0 H1.
discriminate H0.
Qed.



(******************************************************************************)
(* Exercice 5 : terminer les preuves avec "induction" quand nécessaire        *)
(******************************************************************************)

(* Hint : utiliser discriminate pour les cas impossibles après induction sur l et sur l' *)
Lemma concat_nil : forall l l':nlist, l ++ l' = [] -> l = [] /\ l' = [].
Proof.
  intros.
  destruct l.
  * split.
    - reflexivity.
    - simpl in H.
      assumption.
  * split.
    - discriminate.
    - simpl in H.
      destruct l'.
      + reflexivity.
      + discriminate.
(* NB : on remarque que destruct suffit : induction n'est pas nécessaire
   car les hypothèses d'induction ne sont pas utiles pour ce lemme *)
Qed.

(* Hint : utiliser rewrite avec l'hypothèse d'induction *)
Lemma concat_assoc : forall l1 l2 l3, l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros.
  induction l1.
  * simpl.
    intros.
    reflexivity.
  * simpl.
    rewrite IHl1.
    reflexivity.
Restart.
induction l1; trivial.
intros; simpl; rewrite IHl1; trivial.
Restart.
(* dans la lib std c'est écrit comme ça, avec la tactic "f_equal" *)
intros l m n; induction l; simpl; f_equal ; auto.
Qed.

(******************************************************************************)
(* Exercice 6 : fonction de longueur des listes                               *)
(******************************************************************************)

Fixpoint length (l : nlist) : nat :=
  match l with
  | []     => 0 
  | x :: l => S(length l) 
  end.

Compute (length [5;3]).

Lemma length_of_concat : forall l1 l2, length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  * simpl.
    reflexivity.
  * simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma length_zero_ssi_vide (l : nlist) : length l = 0 <-> l=[].
Proof.
split; induction l; intros H; auto; discriminate H.
Qed.


Fixpoint foldr (B:Type) (z:B) (f:nat -> B -> B) (l : nlist) : B :=
  match l with
  | []     => z
  | x :: l' => f x (foldr _ z f l')
  end.

Definition length_2 := foldr nat 0 (fun x y => S y).
Check length_2.

Lemma length_2_is_length : forall l, length_2 l = length l.
Proof.
  unfold length_2; induction l as [ |n l' IHl]; auto.
  simpl; rewrite IHl; auto.
Qed.


End my_list.



(******************************************************************************)
(* Exercice 7 : les arbres binaires (POUR ALLER PLUS LOIN)                    *)
(******************************************************************************)

Section BinTree.

(* éléments dans les noeuds de l'arbre *)
Context {E:Set}.

(* le type inductif *)
Inductive BinTree : Set :=
  | leaf : BinTree 
  | node : BinTree -> E -> BinTree -> BinTree.

(**********************************************************************)
(* On va résoudre la question 3 de l'exo 2 du TD2 de LIFLC            *)

(* Montrer par induction sur Bin E qu'un arbre binaire comportant
   n occurrences de l’arbre vide contient n - 1 éléments              *)
(**********************************************************************)

(* les deux fonctions qui comptent *)
Fixpoint count_leaves (t:BinTree) : nat :=
match t with
 | leaf       => 1
 | node l e r => (count_leaves l) + (count_leaves r)
end.

Fixpoint count_nodes (t:BinTree) : nat :=
match t with
 | leaf       => 0
 | node l e r => 1 + (count_nodes l) + (count_nodes r)
end.

(* la propriété *)
Lemma count_leaves_nodes : forall (t:BinTree), 1 + (count_nodes t) =  (count_leaves  t).
Proof.
induction t.
 - trivial.
 - simpl. rewrite <- IHt1. simpl. rewrite <- IHt2. simpl. rewrite <- plus_n_Sm. trivial.
Qed.
