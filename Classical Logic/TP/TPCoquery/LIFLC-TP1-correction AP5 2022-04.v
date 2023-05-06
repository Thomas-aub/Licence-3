Require Import Utf8.

Section LIFLC_TP1.

(* On introduit les variables avec lesquelles on va travailler par la suite *)
Hypothesis P Q R: Prop.

(**********************************************************************)
(*                                                              *******)
(* CORRECTION DES TP COQ Printemps 2022 : Regarder dans COQUERY *******)
(*                                                              *******)
(**********************************************************************)

(* Exercice 1 *)

(* Compléter la preuve de l'exercice 1 *)
Theorem exercice_1a: (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intro HPQ.
  intro HQR.
  intro HP.
  apply HQR.
  apply HPQ.
  exact HP.
  Restart.
  (* en donnant ici le terme de preuve (de la composition) *)
  exact (fun f g x => g(f(x))).
Qed.

(* Une variante de la précédente avec /\ *)
Theorem exercice_1b: (P -> Q) /\ (Q -> R) -> (P -> R).
Proof.
  intro HPQR.
  destruct HPQR.
  intro HP.
  apply H0.
  apply H.
  exact HP.
Qed.

Check (and P Q).
Print and.
Check conj.

Theorem ex_falso_quodlibet : False ->  P.
Proof.
intros H.
destruct H.
Qed.

(* Compléter la preuve de l'exercice 1c *)
Theorem exercice_1_c: (P \/ Q) -> (Q \/ P).
Proof.
intros H.
destruct H.
right.
apply H.
apply or_introl.
apply H.
Show Proof.
Restart.
exact (λ H : P ∨ Q,
 match H with
 | or_introl H0 => or_intror H0
 | or_intror H0 => or_introl H0
 end).
Restart. (* ou avec le principe d'induction *)
exact (or_ind (@or_intror Q P) (@or_introl Q P)).
Qed.

Print or.

(**********************************************************************)
(* Exercice 2 *)

(* Généralisation du passage de l'exercice 1 à l'exercice 1b *)
(* Cela peut également s'écrire (P -> Q -> R) <-> (P /\ Q -> R) *)
(* Ce théorème est lié à la curryfication vue en LIFAP5 *)
(* Utiliser la tactique split pour traiter un /\ à démontrer. *)
Theorem exercice_2_a: ((P -> Q -> R) -> (P /\ Q -> R)) /\ ((P /\ Q -> R) -> (P -> Q -> R)) .
Proof.
  split.
* intros HPQR HPQ.
  destruct HPQ.
  apply HPQR; assumption.
  (* fin du premier sens *)
* intros HPQR HP HQ.
  apply HPQR.
  split; assumption.
Qed.

Theorem curry : (P -> Q -> R) <-> (P /\ Q -> R).
Proof.
exact (conj (fun f x => f (proj1 x) (proj2 x)) (fun h p q => h (conj p q))).
Qed.


Theorem exercice_2b: (P -> Q) /\ (P -> R) <-> (P -> Q /\ R).
Proof.
  split.
  * intro HCj.
    intro HP.
    destruct HCj as [HPQ HPR].
    split.
    + apply HPQ.
      exact HP.
    + apply HPR.
      exact HP.
  (* fin du premier sens *)
  * intro HPQR.
    split; intro HP; apply HPQR; assumption.
    (* ou plus explicite,, sans utiliser ';'
    + intro HP.
      apply HPQR.
      assumption.
    + intro HP.
      apply HPQR.
      assumption. *)
  Restart.
  tauto.
  Show Proof. (* le terme de preuve *)
  Restart. (* qui sera plus clair ainsi *)
  split.
  exact (λ fg x, conj ((proj1 fg) x) ((proj2 fg) x)).
  exact (λ f, conj (λ p,  proj1 (f p)) (λ p, proj2 (f p))).
  Show Proof.
Qed.

Theorem exemple_avec_items_reset_et_pt_virg: P /\ Q -> P /\ Q.
Proof.
  intro HPQ.
  split.
  * elim HPQ.
    intro HP.
    intro HQ.
    assumption.
  * elim HPQ.
    intro HP.
    intro HQ.
    assumption.
  Restart.
  intro HPQ.
  split; elim HPQ; intros HP HQ; assumption.
  Restart.
  (* avec la tactique Destruct au lieu de elim qui ne modifie pas le but *)
  intro HPQ; destruct HPQ; split; assumption.
  Restart.
  (* ou directement avec exact *)
  intro H; exact H.
  Restart.
  exact (fun x => x). 
Qed.

Theorem exercice_2_c: (~P \/ ~Q) -> ~(P /\ Q).
Proof.
unfold not.
intros H HPQ.
destruct HPQ as [HP HQ].
destruct H; apply H; assumption.
Qed.

Theorem exercice_2_d: ~(P \/ Q) <-> (~P /\ ~Q).
Proof.
split; intros H.
 - split; intros Hn; apply H.
   left; assumption.
   right; assumption.
 - intros Hn. destruct H as [HP HQ].
   destruct Hn.
   apply HP; assumption.
   apply HQ; assumption.
Qed.
(**********************************************************************)
(* Exercice 3 *)

Context (Tiers_exclus: forall X: Prop, X \/ ~X).

(* Utilisation du tiers exclus pour montrer *)
Theorem exercice_3_a: (~(P /\ Q) <-> ~P \/ ~Q).
Proof.
  split.
  + intro NPQ.
    destruct (Tiers_exclus P).
    * right.
      intro HQ.
      apply NPQ.
      split; assumption.
    * left.
      assumption.
  + exact exercice_2_c.
Qed.

Theorem exercice_3_b: ((P -> Q) -> P) -> P.
Proof.
  intros PQP.
  destruct (Tiers_exclus P).
  *  assumption.
  *  apply PQP.
     intro HP.
     contradiction.
Qed.

Theorem exercice_3_c: (~~P <-> P).
Proof.
split.
 - intros H.
   destruct (Tiers_exclus P).
   * trivial.
   * apply ex_falso_quodlibet.
     exact (H H0).
 - intros H Hn. (* sens constructif *)
   exact (Hn H).
Qed.

Theorem exercice_3_d: (~P \/ Q) <-> (P -> Q).
Proof.
split; intros H.
- intros Hp. destruct H.
  * destruct (H Hp).
  * assumption.
- destruct (Tiers_exclus P).
  * right; apply H; assumption.
  * left; assumption.
Qed.

End LIFLC_TP1.
