(* TP4 Langages formels *)

(******************************************************************************)
(************************ grammaires et automates en Coq **********************)
(******************************************************************************)

(* L'objectif de ce TP est de reprendre la définition des automates vue au TP précédent,
   d'ajouter la définition d'une grammaire équivalente et de prouver que l'automate
   et la grammaire sont effectivement équivalents.
*)


(* On commence par rappeler ce qu'on avait défini dans le TP2 *)

(* Notre alphabet d'exemple *)
Inductive Alphabet : Type :=
| a : Alphabet
| b : Alphabet.

(* La fonction "comp_alphabet" de comparaison de deux Alphabet *)
Definition comp_alphabet (x y : Alphabet) : bool :=
  match x with
  | a => match y with
         | a => true
         | b => false
         end
  | b => match y with
         | a => false
         | b => true
         end
end.

Require Export List.
Import ListNotations.

(* La fonction "appartient" qui teste si un entier appartient à une liste d'entiers *)
Fixpoint appartient (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | h::rl => (Nat.eqb x h) || (appartient x rl)
  end.

(* La fonction "trouve" qui prend en paramètres une listes de paires (clef,valeur)
   et une clef k, et renvoie la première valeur associée à k quand elle existe et None sinon
*)
Fixpoint trouve (assoc : list (Alphabet * nat)) (key : Alphabet) : option nat :=
  match assoc with
    | [] => None
    | h::rassoc => if (comp_alphabet key (fst h)) then (Some (snd h))
                   else trouve rassoc key
  end.


(* Le type Automate représentant ce quintuplet. *)
Inductive Automate : Type :=
    automate : list nat -> list Alphabet -> (nat -> Alphabet -> option nat) -> nat -> list nat -> Automate.

(* "etats" : prend en paramètre un automate et renvoie la liste des états *)
Definition etats (M : Automate) :  list nat :=
  match M with
    automate ql _ _ _ _ => ql
  end.

(* "symboles" : prend en paramètre un automate et renvoie la liste des symboles de l'alphabet *)
Definition symboles (M : Automate) :  list Alphabet :=
  match M with
    automate _ sigma _ _ _ => sigma
  end.

(* "initial" : prend en paramètre un automate et renvoie l'état initial *)
Definition initial  (M : Automate) :  nat :=
  match M with
    automate _ _ _ q0 _ => q0
  end.

(* "acceptant" : prend en paramètre un automate et un état et renvoie "true" SSI q est un état final *)
Definition acceptant  (M : Automate) (q : nat) : bool  :=
  match M with
    automate _ _ _ _ lF => (appartient q lF)
  end.

(* "transition" : prend en paramètre un automate, un état et un symbole, et renvoie l'état (optionnellement)
   accessible depuis "q" en lisant "c" *)
Definition transition  (M : Automate) (q : nat) (c : Alphabet) : option nat :=
  match M with
    automate _ _ f _ _ => f q c
  end.

(* La fonction "execute" qui va calculer l'état d'arrivée en lisant un mot, c'est-à-dire une "list Alphabet" *)
Fixpoint execute (M : Automate)  (q : nat) (w : list Alphabet) : option nat :=
  match w with
  | [] => Some q
  | h::rw => match transition M q h with
             | None => None
             | Some e => execute M e rw end
  end.

(* La fonction "reconnait" qui va accepter ou refuser un mot *)
Definition reconnait (M : Automate) (w : list Alphabet) : bool :=
  match (execute M (initial M) w) with
  | None => false
  | Some e => acceptant M e
  end.


(* L'automate "M_nb_b_impair" à deux états qui accepte les mots contenant un nombre impair de 'b' *)
Definition delta_nb_b_impair (q : nat) (c : Alphabet) : option nat :=
match (q,c) with
 | (1,a) => Some 1
 | (1,b) => Some 2
 | (2,a) => Some 2
 | (2,b) => Some 1
 | (_,_) => None
end.
Definition M_nb_b_impair := automate [1;2] [a;b] (delta_nb_b_impair) 1 [2].


(* L'automate "M_commence_et_finit_par_a" à trois états qui accepte les mots commençant et finissant par 'a' *)
Definition delta_commence_et_finit_par_a (q : nat) (c : Alphabet) : option nat :=
match (q,c) with
 | (1,a) => Some 2
 | (2,a) => Some 2
 | (2,b) => Some 3
 | (3,a) => Some 2
 | (3,b) => Some 3
 | (_,_) => None
end.
Definition M_commence_et_finit_par_a := automate [1;2;3] [a;b] (delta_commence_et_finit_par_a) 1 [2].


(* ------------------------------------------------------------ *)


(* Fin des rappels. Ici commence le TP4. *)

(* L'automate M_nb_b_impair implémente la grammaire G_nb_b_impair suivante :
   S1 -> a S1
   S1 -> b S2
   S2 -> a S2
   S2 -> b S1
   S2 -> epsilon
*)

(* G_nb_b_impair w i : c'est le le <blink> PRÉDICAT </blink> "mot généré par G_nb_b_impair à partir du non-terminal Si" *)
Inductive G_nb_b_impair : (list Alphabet) -> nat -> Prop :=
| G_nb_b_impair_0 : G_nb_b_impair [] 2
| G_nb_b_impair_1a : forall w, G_nb_b_impair w 1 -> G_nb_b_impair (a::w) 1 
| G_nb_b_impair_1b : forall w, G_nb_b_impair w 2 -> G_nb_b_impair (b::w) 1 
| G_nb_b_impair_2a : forall w, G_nb_b_impair w 2 -> G_nb_b_impair (a::w) 2
| G_nb_b_impair_2b : forall w, G_nb_b_impair w 1 -> G_nb_b_impair (b::w) 2.

(* EXERCICE *)
(* Comprendre et expliquer en langue naturelle comment est construit et comment fonctionne ce prédicat. *)


(* G_nb_b_impair génère le mot abaabab à partir du non-terminal S1 *)
Example ex_G_nb_b_impair_1 : G_nb_b_impair [a;b;a;a;b;a;b] 1.
Proof.
  (* repeat constructor.*)
  apply G_nb_b_impair_1a. (* état courant 1, symbole courant a -> état 1, reste baabab *)
  apply G_nb_b_impair_1b. (* état courant 1, symbole courant b -> état 2, reste aabab *)
  apply G_nb_b_impair_2a. (* état courant 2, symbole courant a -> état 2, reste abab *)
  apply G_nb_b_impair_2a. (* état courant 2, symbole courant a -> état 2, reste bab *)
  apply G_nb_b_impair_2b. (* état courant 2, symbole courant b -> état 1, reste ab *)
  apply G_nb_b_impair_1a. (* état courant 1, symbole courant a -> état 1, reste b *)
  apply G_nb_b_impair_1b. (* état courant 1, symbole courant b -> état 2, reste epsilon *)
  apply G_nb_b_impair_0.
Qed.

(* G_nb_b_impair génère le mot baab à partir du non-terminal S2 *)
Example ex_G_nb_b_impair_2 : G_nb_b_impair [b;a;a;b] 2.
Proof.
  apply G_nb_b_impair_2b.
  apply G_nb_b_impair_1a.
  apply G_nb_b_impair_1a.
  apply G_nb_b_impair_1b.
  apply G_nb_b_impair_0.
Qed.

(* Evidemment, _nb_b_impair1 ne peut pas générer, par exemple, le mot bab à partir du non-terminal S1. *)


(* EXERCICE *)
(* Définir la grammaire G_commence_et_finit_par_a implémentée par l'automate M_commence_et_finit_par_a,
   et donner des exemples de mots générés par cette grammaire. *)
Inductive G_commence_et_finit_par_a  : (list Alphabet) -> nat -> Prop :=
| G_commence_et_finit_par_a0 : G_commence_et_finit_par_a [] 3
| G_commence_et_finit_par_a1  : forall w, G_commence_et_finit_par_a w 2 -> G_commence_et_finit_par_a (a::w) 1
| G_commence_et_finit_par_a2a : forall w, G_commence_et_finit_par_a w 2 -> G_commence_et_finit_par_a (a::w) 2
| G_commence_et_finit_par_a2b : forall w, G_commence_et_finit_par_a w 2 -> G_commence_et_finit_par_a (b::w) 2
| G_commence_et_finit_par_a2c : forall w, G_commence_et_finit_par_a w 3 -> G_commence_et_finit_par_a (a::w) 2.


Example ex_G_commence_et_finit_par_a_1 : G_commence_et_finit_par_a [a;b;a;b;a;a;b;a] 1.
Proof.
  apply G_commence_et_finit_par_a1.
  apply G_commence_et_finit_par_a2b.
  apply G_commence_et_finit_par_a2a.
  apply G_commence_et_finit_par_a2b.
  apply G_commence_et_finit_par_a2a.
  apply G_commence_et_finit_par_a2a.
  apply G_commence_et_finit_par_a2b.
  apply G_commence_et_finit_par_a2c.
  apply G_commence_et_finit_par_a0.
Qed.

(* ------------------------------------------------------------ *)

(* Equivalence grammaire et automate *)

(* On veut prouver :
   "Soit un automate M qui implémente une grammaire G.
    G génère un mot w à partir de S1 ssi M accepte w."

   EN PARTICULIER :
   "G_nb_b_impair génère un mot w à partir de S1 ssi M_nb_b_impair accepte w."

   ET :
   "G_commence_et_finit_par_a génère un mot w à partir de S1 ssi M_commence_et_finit_par_a accepte w."
*)


(* 1. Sens Automate => Grammaire *)

(* On sait trouver une exécution par dérivation : *)
(* Si G permet de générer un mot w à partir du non-terminal Sq,
      alors M accepte w à partir de l'état q *)

(* EXERCICE *)
(* Montrer que si G_nb_b_impair génère un mot w à partir du non-terminal Sq,
    alors M_nb_b_impair accepte ce mot w à partir de l'état q. *)
Lemma G_nb_b_impair_mime_M_nb_b_impair :
  forall w q, G_nb_b_impair w q
  -> exists e, execute M_nb_b_impair q w = Some e /\ acceptant M_nb_b_impair e = true.
Proof.
  intro w.
  intro q.
  intro hpredi.
  induction hpredi as [|w hregu' Ihregu'|w hregu' Ihregu'| w hregu' Ihregu'|w hregu' Ihregu'].
  - exists 2.
    split.
    + simpl.
    reflexivity.
    + simpl.
     reflexivity.
  - destruct Ihregu'. 
    exists x.
    split.
     + simpl.
        destruct H.
        assumption.
      + destruct H.
        assumption.
  - destruct Ihregu'.
    exists x.
    split.
     + simpl.
        destruct H.
        assumption.
      + destruct H.
        assumption.
  - destruct Ihregu'.
    exists x.
    split.
     + simpl.
        destruct H.
        assumption.
      + destruct H.
        assumption.
  - destruct Ihregu'.
    exists x.
    split.
     + simpl.
        destruct H.
        assumption.
      + destruct H.
        assumption.
Qed.


(* EXERCICE à faire chez vous*)
(* Même exercice avec la grammaire G_commence_et_finit_par_a *)

(* Tout mot w généré par G à partir de la source est reconnu par M. *)
(* Si G génère un mot w à partir du non-terminal S1, alors M accepte w *)

(*
Inductive G_commence_et_finit_par_a  : (list Alphabet) -> nat -> Prop :=
| G_commence_et_finit_par_a0 : G_commence_et_finit_par_a [] 3
| G_commence_et_finit_par_a1  : forall w, G_commence_et_finit_par_a w 2 -> G_commence_et_finit_par_a (a::w) 1
| G_commence_et_finit_par_a2a : forall w, G_commence_et_finit_par_a w 2 -> G_commence_et_finit_par_a (a::w) 2
| G_commence_et_finit_par_a2b : forall w, G_commence_et_finit_par_a w 2 -> G_commence_et_finit_par_a (b::w) 2
| G_commence_et_finit_par_a2c : forall w, G_commence_et_finit_par_a w 3 -> G_commence_et_finit_par_a (a::w) 2.
*)
(* L'automate devrait etre acceptant au niveau de l'état 2*)

(*
Lemma G_commence_et_finit_par_a_mime_M_commence_et_finit_par_a :
  forall w q, G_commence_et_finit_par_a w q
  -> exists e, execute M_commence_et_finit_par_a q w = Some e /\ acceptant M_commence_et_finit_par_a e = true.
Proof.
  intro w.
  intro q.
  intro hpredi.
  induction hpredi as [|w hregu Ihregu|w hregu Ihregu| w hregu Ihregu|w hregu Ihregu].
  - exists 3.
    split.
    + simpl.
      reflexivity.
    + simpl.
      
      *)



(* EXERCICE *)
(* Montrer que si G_nb_b_impair génère un mot w, alors M_nb_b_impair accepte ce mot w. *)
(* HINT. C'est un cas particulier du théorème précédent *)
Lemma G_nb_b_impair_reco_M_nb_b_impair :
  forall w, G_nb_b_impair w 1 -> reconnait M_nb_b_impair w = true.
Proof.
  intro w.
  intro q.
  induction
Qed.

(* 2. Sens grammaire => automate *)

(* On sait trouver une dérivation par exécution. *)
(* Si q est un état valide de M
   alors si M accepte un mot w à partir de l'état q, alors G génère w à partir de son non-terminal Sq *)
Require Import Arith.
Check EqNat.beq_nat_true.

(* EXERCICE *)
(* Montrer que si M_nb_b_impair accepte un mot à partir d'un état valide, alors G_nb_b_impair génère ce mot. *)
Lemma M_nb_b_impair_mime_G_nb_b_impair :
  forall w q, (appartient q (etats M_nb_b_impair)) = true
  -> (forall e, execute M_nb_b_impair q w = Some e /\ acceptant M_nb_b_impair e = true
         -> G_nb_b_impair w q).
Proof.
Admitted.


(* Remarque : le théorème précédent pourrait être formulé de la manière suivante : voici le corollaire *)
Lemma M_nb_b_impair_mime_G_nb_b_impair' :
  forall w q, (appartient q (etats M_nb_b_impair)) = true
  /\ (forall e, execute M_nb_b_impair q w = Some e /\ acceptant M_nb_b_impair e = true)
         -> G_nb_b_impair w q.
Proof.
intros w q H.
destruct H as [H1 H2].
apply M_nb_b_impair_mime_G_nb_b_impair with (e := 2).
- exact H1.
- apply H2.
Qed.


(* EXERCICE à faire chez vous*)
(* Même exercice avec l'automate M_commence_et_finit_par_a *)


(* Tout mot w reconnu par M est généré par G à partir de la source. *)
(* Si M accepte w, alors G génère w à partir du non-terminal S1. *)

(* EXERCICE *)
(* Montrer que si M_nb_b_impair accepte un mot w, alors G_nb_b_impair génère ce mot w à partir de S1. *)
Lemma M_nb_b_impair_regu_G_nb_b_impair :
  forall w, reconnait M_nb_b_impair w = true -> G_nb_b_impair w 1.
Proof.
Admitted.


(* FIN DU TP4 *)


