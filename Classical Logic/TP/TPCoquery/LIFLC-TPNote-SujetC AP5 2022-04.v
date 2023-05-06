


(***************************** LIFLF - TPNOTE *********************************)
(************* Evaluation pratique en temps limité : 30' **********************)

(************************ SUJET D'ENTRAINEMENT ********************************)
(* Ce sujet est représentatif de celui qui vous sera donné à réaliser en temps 
limité. Les fonctions lemmes demandés ici sont tout à fait classiques.
*)
Require Import Utf8.


(******************************************************************************)
(* Logique propositionnelle *)
(******************************************************************************)
Section PL.

Context (P Q : Prop).

(* EXERCICE : prouver la propriété suivante SANS UTILISER UNE TACTIQUE AUTOMATIQUE *)
Lemma de_morgan : (~P \/ ~Q) -> ~(P /\ Q).
unfold not.
intro pq.
destruct pq as [hp | hq].
- intro f.
  apply hp.
  destruct f.
  assumption.
- intro hpq.
  destruct hpq.
  apply hq.
  assumption.
Qed.

End PL. 

(******************************************************************************)
(* Les listes *)
(******************************************************************************)

Print length. (* la longueur de listes *)
Check length.

Check nil.

(* EXERCICE :  énoncer le lemme "mystere" en langue naturelle *)
Lemma mystere A:  forall l : list A, length l = 0 <-> l = nil.
intro l.
split.
- intro len.
Check length.
  + pose (length l).



(* EXERCICE :  prouver le lemme "mystere"  SANS UTILISER "Require Import List." *)








