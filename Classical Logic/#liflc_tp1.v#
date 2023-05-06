(* LES SEULES COMMANDES AUTORISÉES SONT CELLES DÉCRITES DANS CE FICHIER. *)


(* Les indications entre "" ne sont pas à recopier, elles indiquent
   juste que vous avez à mettre un nom à cet endroit. *)


(* On introduit les variables propositionnelles avec lesquelles 
   on va travailler par la suite *)
Context (P Q R A Z J F M S T: Prop).

(**********************************************************************)
(* Exercice 1 LA FLÈCHE  ***********************)
(* - axiome : assumption
   - introduction de la flèche : intro "nom qu'on donne à l'hypothèse" 
   - élimination de la flèche : apply "nom de l'hypothèse utilisée" *)
Theorem exercice_1a: P -> (P -> Q) -> Q.
Proof.
  intro hp.
  intro hpq.
  apply hpq.
  assumption.
Qed.


Theorem exercice_1b: (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intro hp.
  intro hpq.
  intro hpqr.
  apply hpq.
  apply hp.
  assumption.
  
Qed.

(* Exercice 2 LE ET  ***********************)
(* Une variante de la question précédente avec /\ *)
(* - décomposition du /\ en hypothèse : destruct "nom de l'hypothèse avec /\" as [ "nom gauche" "nom droite" ]
*)
Theorem exercice_2a: (P -> Q) /\ (Q -> R) -> (P -> R).
Proof.

  intro hi.
  destruct hi as [hpq hqd].
  intro hpr.
  apply hqd.
  apply hpq.
  assumption.
Qed.

(* - introduction du /\ : split *)
(* On obtient bien deux sous-buts *)
Theorem exercice_2b : P -> Q -> P /\ Q.
Proof.
  split.
  assumption.
  assumption.
Qed.
  
(* Exercice 3 LE OU  ***********************)
(* introduction du ou :
   - depuis la droite : right
   - depuis la gauche : left

   decomposition du \/ en hypothèse : destruct "nom de l'hypothèse avec \/" as [ "nom gauche" | "nom droite" ]
   notez le | qui sépare les sous-buts. *)

Theorem exercice_3a: (P \/ Q) -> (Q \/ P).
Proof.
  intro hi.
  destruct hi as [hp|hq].
  - right.
   assumption.
  -left.
  assumption.

  
Qed.

(* À partir de maintenant on nommera SYSTÉMATIQUEMENT les hypothèses qui
apparaissent dans les destruct avec "as" et suivant le nombre de sous-buts *)
(* ---------------------------------------------------------------------*)


(* zéro constructeur *)
Print False. 
(* un seul constructeur car une seule règle d'intro *)
Print and.
(* deux constructeurs car deux règles d'intro*)
Print or.  

(* destruct donne bien un sous but par constructeur *)
(* On remarque que comme False n'a aucun constructeur : le destruct
résoud le but *)
Theorem ex_falso_quodlibet : False ->  P.
Proof.
  intro Hfp.
  destruct Hfp.
   
Qed.

(** un peu difficile **)
(* Plus généralement, la tactique exfalso remplace tout but par False. *)
(* Si on peut déduire False des hypothèses, c'est alors gagné ! *)

Theorem ex_falso_quodlibet_Q : (A -> False) -> A -> (P \/ (Q -> Z /\ J) -> F).
Proof.
  intro Haf.
  intro Hap.
  exfalso.
  apply Haf.
  assumption.
Qed.

Print exercice_1a.
  

(* ---------------------------------------------------------------------*)


(* Exercice 4 PREMIÈRE MODÉLISATION  ***********************)
(* Modéliser l'exercice de TD "Zoé va à Paris", prouver que Zoé va à Paris *)
(* - introduction du /\ : split
*)

Theorem zoe_va_a_paris : (A /\ J -> Z) -> (J -> A) -> (Z \/ J) -> Z.
Proof.
  intro Hajz.
  intro Hja.
  intro Hzjz.
  destruct Hzjz as [Hz|Hj].
  - assumption.
  - apply Hajz.
    split.
    apply Hja.
      assumption.
    assumption.
  

Qed.

(* Exercice 5 LE NOT *************************)

(* - la notation not : unfold not
   - la notation not en hypothèse : unfold not in "nom de l'hypothèse avec le ~ "
*)
Theorem exercice_5a : (~P \/ ~Q) -> ~(P /\ Q).
Proof.
  unfold not.
  intro npq.
  destruct npq as [hpq|hqd].
  - intro fa.
    destruct fa as [hp hq].
    apply hpq.
    assumption.
  - intro fa.
    apply hqd.
    destruct fa as [hp hq].
    assumption.
Qed.
(* on voit qu'on passe son temps à faire des unfold dans chacun des sous-buts, il aurait donc mieux valu *commencer* par ce unfold, avant l'introduction de la flèche *)


(* Si on a toto et ~toto dans les hypothèses, alors le but est résolu avec "contradiction." *)
(* c'est juste un raccourci pour exfalso. apply "hypothèse avec le -> False". assumption. *)
Theorem exercice_5b : P -> ~P -> Q.
Proof.
  intro hpq.
  intro  hq.
  exfalso.
  apply hq.
  assumption.
Qed.

(**********************************************************************)
(* Exercice 6 LE TIERS-EXCLU *)

(* On introduit la règle de tiers-exclu. *)
Context (Tiers_exclus: forall X: Prop, X \/ ~X).

(* Pour l'utiliser, c'est-à-dire pour avoir deux sous buts, un avec toto en hypothèse, l'autre avec ~toto, on invoquera :
   destruct (Tiers_exclus toto) as [ "nom_hyp" | "nom_hyp ~" ].
*)


Theorem exercice_6a: ((P -> Q) -> P) -> P.
Proof.
  intro hp.
  destruct (Tiers_exclus P) as [ hpq| hpqf ].
  - assumption.
  - apply hp.
    intro hq.
    exfalso.
    apply hpqf.
    assumption.
Qed.

(* Deuxième modélisation *)
(* Modéliser l'exercice de TD "Frodon va au Mordor", prouver que Frodon est triste *)

Theorem exercice_6b : (~F -> S) -> (S -> T) -> (F -> ~A) -> (~A -> T) -> T.
Proof.
  intro hs.
  intro ht.
  intro ha.
  intro hat.
  destruct (Tiers_exclus F) as [ df| dff].
  - apply hat.
    apply ha.
    assumption.
  - apply ht.
    apply hs.
    assumption.


  
Qed.


(* Quid de ~~P et P ? *)
Theorem exercice_6c: (~~P -> P) /\ (P -> ~~P).
(* Pour l'un des deux sens on aura besoin du tiers-exclu et, en remarquant qu'on peut déduire False des hypothèses, de la simplification "exfalso". *)

Proof.
  split.
  - intro hp.
  destruct (Tiers_exclus P) as [ dp| dpf].
  assumption.
  unfold not in hp.
  unfold not in dpf.
  exfalso.
  apply hp.
  assumption.
  - intro hp.
    unfold not.
    intro hf.
    apply hf.
    assumption.
    
  
  
Qed.

























