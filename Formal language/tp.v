Require Import Arith.
Require Import List.
Export ListNotations.


(* Fonction "lgr" qui calcule la longueur d'une liste de nat (et donc de type list nat) *)
Fixpoint lgr (l : list nat) : nat :=
match l with
| [] => 0
| e::l1 => (lgr l1)+1
end.

Example ex_lgr : (lgr (1::2::3::4::5::[])) = 5.
Proof. simpl. reflexivity. Qed.

(* Fonction "mir" qui calcule le miroir d'une liste de nat *)
Fixpoint mir (l : list nat) : list nat :=
match l with
| [] => []
| e::l1 => (mir l1)++[e]
end.

(* dans la vraie vie on ne fera jamais de concatÃ©nation de ce type mais ce n'est pas le problÃ¨me ici *)

Example ex_mir : (mir (1::2::3::4::5::[])) = 5::4::3::2::1::[].
Proof. simpl. reflexivity. Qed.

(* On rappelle le type "btree" des arbres binaires avec valeurs de type nat stockÃ©es dans les feuilles *)
Inductive btree : Type :=
| F : nat -> btree
| N : btree -> btree -> btree
.

(* Fonction "bsumval" qui calcule la somme des valeurs contenues dans l'arbre *)
Fixpoint bsumval (b : btree): nat :=
match b with 
| (F n) => n
| (N f1 f2) => (bsumval f1) + (bsumval f2)
end.

(* Fonction "bajout" qui ajoute un Ã©lÃ©ment dans un arbre *)
(* plusieurs solutions sont possibles... *)
Definition bajout (a: nat)(b : btree) : btree:=
match b with 
| f => (N f (F a))
end.

(* exemples *)
(* on peut dÃ©finir "ab1" :  o
                           / \
                          o   2
                         / \
                        1   o
                           / \
                          o   3
                         / \
                        4   5
*)

Definition ab1 := N (N (F 1) (N (N (F 4) (F 5)) (F 3))) (F 2).

Example ex_bsumval_ab1 : (bsumval ab1) = 15.
Proof. cbv. reflexivity. Qed.

(*************** LOGIQUE CLASSIQUE ***************)

Context (E H G : Prop).

(* EXERCICE *)
(* Prouver les lemmes suivants *)
Lemma LC1 : ((H \/ E) -> G) -> ((E -> G) /\ (H -> G)).
Proof.
intro h1.
split.
- intro e.
  apply h1.
  right.
  assumption.
- intro h.
  apply h1.
  left.
  assumption.
  
Qed.


Lemma LC2 : (H \/ E) -> ((E -> H) -> H).
Proof.
  intro he.
  intro eh.
  destruct he as [h|e].
  - assumption.
  - apply eh.
    assumption.
Qed.

Lemma plus : forall a b c : nat, a + b + c = a + c + b.
Proof.
intros.
induction a.
 - simpl.
   pose (Nat.add_comm b c ).
  rewrite e.
  reflexivity.
 - simpl.
  rewrite IHa.
  reflexivity. 
Qed.


(* EXERCICE *)
(* Exprimer et montrer que la longueur de la concatÃ©nation de deux listes de nat (donc de type list nat)  est la somme des longueurs des concatÃ©nÃ©s*)
Lemma concat_compat : forall l1 l2 : list nat, (lgr (l1++l2)) = (lgr l1) + (lgr l2).
Proof.
intros.
induction l1.
- simpl.
  reflexivity.
- simpl.
  rewrite -> IHl1.
  pose (Nat.add_comm (lgr l1) (1 + (lgr l2)) ).
  pose (plus (lgr l1) (lgr l2) 1).
  rewrite e0.
  reflexivity.
Qed.

   


(* EXERCICE *)
(* Montrer que la longueur d'une liste c'est la longueur de son miroir *)
(* On pourra avoir besoin de la commutativitÃ© de l'addition, donnÃ©e par le lemme Nat.add_comm, et dulemme prÃ©cÃ©dent *)

Check Nat.add_comm.

Lemma lgrmireq : forall l : list nat, (lgr (mir l)) = (lgr l).
Proof.
intros.
induction l.
- simpl.
  reflexivity.
- simpl.
  pose (concat_compat( mir l) [a]). 
  rewrite e.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

(* EXERCICE *)
(* Exprimer et montrer que l'addition est associative, c'est-Ã -dire qu'on a (x + y) + z = x + (y + z) pour x, y et z de type nat. *)
(* rappel : ce qui est notÃ© x + y + z (sans parenthÃ¨ses) est en fait (x + y) + z *)
Lemma p_assoc : forall x y z : nat, (x + y) + z = x + (y + z).
Proof.
intros.
induction x.
- simpl.
  reflexivity.
- simpl.
  rewrite IHx.
  reflexivity.
Qed.


(* EXERCICE *)
(* Exprimer et montrer que la somme des valeurs d'un arbre t Ã  laquelle on additionne un nat e est Ã©gale Ã  la somme des valeurs de l'arbre t dans lequel on a ajoutÃ© un Ã©lÃ©ment de valeur e. *)

(* On pourra avoir besoin de la commutativitÃ© de l'addition, donnÃ©e par le lemme Nat.add_comm, et de l'associativitÃ© dÃ©montrÃ©e auparavant. *)

Check Nat.add_comm.

Lemma bsumcons_compat : forall b : btree, forall n : nat, (bsumval (bajout n b)) = (bsumval b) + n .
Proof.
intros.
simpl.
reflexivity.
Qed.

