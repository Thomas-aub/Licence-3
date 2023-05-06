
Require Import Utf8.
Require Import List.
Require Import Bool.
Require Import Arith.
Import ListNotations.

(***************************** LIFLC - TP3 ************************************)
(********** de la preuve en langue naturelle ou formelle en Coq ***************)
(******************************************************************************)

(* 
   L'objectif de ce TP est de consolider la pratique de la preuve en passant de
   preuves simples vues en TD de logique aux preuves formelles en Coq et vice versa.
   
   Ainsi on définira et on prouvera en Coq
   Partie A : les définitions de base de logique propositionnelle de LIFLC
   Partie B : la relation d'équivalence entre formules
   Partie C : le calcul de la liste des variables d'une formule (un exercice de LIFLC-TD3
   Partie D : exemples des parties A, B et C.
   Partie E : l'exercice sur les arbres du CC1
   Partie F FACULTATIVE : une preuve que les connecteurs ET et NON sont fonctionnellement complets
   Partie G FACULTATIVE (HORS PISTE) : automatisation en Coq
   Partie H FACULTATIVE (HORS PISTE) : lemmes de substitution en Coq

                    /!\ Les exemples sont repoussés en partie D /!\
   /!\ Quand vous avancez dans les parties A, B, C, allez voir si les exemples passent /!\

   Pour se rapprocher des mathématiques usuelles et pour se simplifier la vie,
   on va utiliser l'automatisation en Coq pour résoudre les buts qui sont 'faciles'.
   La pratique de Coq s'améliorant, on hésitera plus à utiliser les tactiques
    - "intros H1 H2 H3" pour introduire plusieurs hypothèses  
    - "intros" (tout court) pour nommer automatiquement les hypothèses
    - "cbn" au lieu de "simpl" 
    - "trivial" et "auto" pour résoudre un but facile par recherche automatique
    - ";" la composition de tactiques pour gérer les sous-buts similaires ou faciles
    - "rewrite H1, H2, ..., Hn" équivalent à "rewrite H1; rewrite H2; ...; rewrite Hn"

*)

(******************************************************************************)
(* PARTIE A. LOGIQUE PROPOSITIONNELLE : TYPE INDUCTIF ET SEMANTIQUE           *)
(******************************************************************************)
Section LogiqueProp.
(* L'ensemble "V" des variables propositionnelles, un paramètre pour toute la suite *)
Context {V:Set}.


(* Les formules de la logique propositionnelle encodée par un type inductif "PL" *)
(* UNE PAUSE S'IMPOSE : on est bien en train de coder, dans le langage de
   programmation fonctionnelle de Coq, *les formules de logique des propositions* *)
Inductive PL  : Set :=
  | VarPL (v:V) : PL            (* cas F = v, avec v ∈ V *)
  | TruePL : PL                 (* cas F = 1 *)
  | FalsePL : PL                (* cas F = 0 *)
  | NotPL (A:PL) : PL           (* cas F = ¬ F1 *)
  | OrPL (A:PL) (B:PL) : PL     (* cas F = F1 \/ F2 *)
  | AndPL (A:PL) (B:PL) : PL.   (* cas F = F1 /\ F2 *)

(* Pour évaluer les formules, leur donner une sémantique, on associe à chaque
   constructeur (i.e., à chaque noeud de l'arbre de syntaxe abstraite)
   une fonction *booléenne*, c'est-à-dire de la forme "bool -> ... -> bool -> bool"
   On utilise bien sûr les fonctions et théorème standards de Coq   
   https://coq.inria.fr/library/Coq.Bool.Bool.html *)
   
Print bool.
Print true.
Print false.
Print negb.
Print orb.  (* notée "||" *)
Print andb. (* notée "&&" *)

(* 
/!\ IL NE FAUT PAS CONFONDRE /!\
 - "bool: Set" qui est le type des booléens en Coq
 - "PL : Set"  qui est notre représentation des formules, la structure de données
               sur laquelle on va calculer
 - "Prop:Type" qui est le type des *énoncés* que l'on va prouver en Coq : des
               formules qui parlent de nos programmes
*)
 
Check bool:Set.
Check PL:Set.
Check Prop:Type.

(* /!\ C'EST UN PEU DEROUTANT /!\ mais on va avoir pour chaque connecteur 
  logique *TROIS* représentants : un dans "bool", un dans "PL" et un dans "Prop"

  - "true  : bool",                "TruePL  : PL",             "True  : Prop"
  - "false : bool",                "FalsePL : PL",             "False : Prop"
  - "negb  : bool → bool",         "NotPL   : PL → PL",        "not   : Prop → Prop" (noté "~")
  - "andb  : bool → bool → bool",  "AndPL   : PL → PL → PL",   "and   : Prop → Prop → Prop" (noté "/\")
  - "orb   : bool → bool → bool",  "OrPL    : PL → PL → PL",   "or    : Prop → Prop → Prop" (noté "\/")

*)


(********************************)
(* EXERCICE : définir la fonction d'évaluation *)
(* REMARQUE : on a donné une définition par défaut, "true" QU'IL FAUT REMPLACER *)
(********************************)
Fixpoint eval (F : PL) (I:V -> bool) : bool :=
true.

(********************************)
(* EXERCICE : aller tester en Partie D que votre fonction est correcte *)
(********************************)

(* Définition de l'équivalence de formules, comme en cours *)
Definition equiv_PL (F1 F2 : PL) : Prop := ∀ I, eval F1 I = eval F2 I.

(* On va introduire une notation *)
Notation "X <=> Y" := (equiv_PL X Y) (at level 45, left associativity).
(* Pour dire à Coq qu'il peut unfold "equiv_PL" tout seul avec "auto" *)
Hint Unfold equiv_PL.

(******************************************************************************)
(* PARTIE B. LOGIQUE PROPOSITIONNELLE : EQUIVALENCE LOGIQUE           *)
(******************************************************************************)

(********************************)
(* EXERCICE : montrer que "<=>" a.k.a. "equiv_PL" est une relation d'équivalence *)
(********************************)

(* " <=>" est réfléxive *)
Lemma equiv_PL_refl : forall (F:PL), F <=> F.
Proof.
Admitted.

(* " <=>" est symétrique *)
Lemma equiv_PL_sym : forall (F1 F2:PL), F1 <=> F2 -> F2 <=> F1.
Proof.
Admitted.

(* Pour la transitivité de "<=>", on va utiliser la tactique "transitivity y" qui
   prend un argument "y". En effet, pour démontrer que "x = z" par transitivité
   il faut démontrer que "x = y " et "y = z". Comme Coq ne peut pas deviner "y",
   il faut lui donner le témoin *)
Lemma equiv_PL_trans : forall (F1 F2 F3:PL), F1 <=> F2 -> F2 <=> F3 -> F1 <=> F3.
Proof.
Admitted.

(********************************)
(* EXERCICE : prouver la loi de De Morgan *)
(* HINT : analyser par cas "(eval F I)" avec la tactique "destruct (eval F I)" *)
(********************************)
Lemma de_morgan_1  : forall (F1 F2:PL), (OrPL F1 F2) <=> (NotPL (AndPL (NotPL F1) (NotPL F2))).
Proof.
Admitted.

(******************************************************************************)
(* PARTIE C. LOGIQUE PROPOSITIONNELLE :  LISTES DES VARIABLES D'UNE FORMULE   *)
(******************************************************************************)

(********************************)
(* EXERCICE : définir la fonction "vars" qui calcule la LISTE des variables d'une formule *)
(* REMARQUE : on a donné une définition par défaut, "[]" QU'IL FAUT REMPLACER *)
(********************************)
Fixpoint vars (F : PL) : list V :=
[].

(* /!\ ATTENTION /!\  "vars" calcule une LISTE de variables et pas un ENSEMBLE,
                       donc l'ordre et la multiplicité comptent ! *)

(********************************)
(* EXERCICE : aller tester en Partie D que votre fonction est correcte *)
(********************************)

(* La relation inductive "In : ∀ A : Type, A → list A → Prop" formalise l'idée 
   d'appartenance d'un élément à une liste : c'est la contrepartie dans "Prop"
   de "appartient" écrite en LIFLF-TP2.
 *)
Print In.

(********************************)
(* EXERCICE : exprimer l'énoncé "vars_or_app" en langue naturelle*)
(********************************)
Lemma vars_or_app : ∀ F1 F2 (I1 I2:V → bool),
  (∀ v, In v (vars F1 ++ vars F2) → I1 v = I2 v) -> 
   (∀ x, In x (vars F1) → I1 x = I2 x) /\ (forall x, In x (vars F2) → I1 x = I2 x) .
Proof.
Admitted.

(********************************)
(* EXERCICE FACULTATIF : prouver "vars_or_app" *)
(* HINT : utiliser "in_app_iff : ∀ (A : Type) (l l' : list A) (a : A), In a (l ++ l') ↔ In a l ∨ In a l'" *)
(********************************)
Check in_app_iff.


(********************************)
(* EXERCICE : donner une expression du théorème "mystere" ci-dessous et donner
              sa preuve rédigée en français *)
(* HINT : fait en TD *)
(********************************)
Lemma mystere : forall F:PL, forall I1 I2 : V -> bool, (forall v,
    In v (vars F) -> I1 v = I2 v) -> eval F I1 = eval F I2.
Proof.
induction F; intros I1 I2 H; auto.
apply H; left; auto.
simpl; rewrite (IHF I1 I2 H); auto.
destruct (vars_or_app F1 F2 I1 I2 H) as [H1 H2]; simpl;
  rewrite <- (IHF1 I1 I2 H1); rewrite -> (IHF2 I1 I2 H2); auto.
destruct (vars_or_app F1 F2 I1 I2 H) as [H1 H2]; simpl;
  rewrite <- (IHF1 I1 I2 H1); rewrite -> (IHF2 I1 I2 H2); auto.
Qed.

(********************************)
(* EXERCICE FACULTATIF (purement sur les listes) : démontrer "in_app_iff'" *)
(********************************)

Lemma in_app_iff' : ∀ (A : Type) (l1 l2 : list A) (a : A), In a (l1 ++ l2) ↔ In a l1 ∨ In a l2.
Proof.
Admitted.


End LogiqueProp.

(* On répète ici car on est sorti de la section *)
Notation "X <=> Y" := (@equiv_PL _ X Y) (at level 45, left associativity).
Hint Unfold equiv_PL.

(******************************************************************************)
(* PARTIE D. EXEMPLES DES PARTIES PRECEDENTES                                 *)
(******************************************************************************)

(********* EXEMPLES DE FORMULES ******************)

(* NOTA BENE : la syntaxe "Context {V:Set}" indique que le paramètre "V" (l'ensemble
   des variables propositionnelles) de "PL" est IMPLICITE : on laisse le soin
   à Coq de le déduire sans l'expliciter. *)

(* un example avec les entiers pour l'ensemble des variables *)
Definition pl_ex_1 : PL :=
  AndPL (OrPL (NotPL (VarPL 0)) (VarPL 1)) TruePL.

(* on utilise la notation "@PL X" pour expliciter "V" quand on le souhaite *)
Definition pl_ex_2 : @PL nat :=
  TruePL.


(********* EXEMPLES D'INTERPRETATIONS ******************)

Definition I_true : nat -> bool := 
fun n => true.
Definition I_false : nat -> bool := 
fun n => false.
Definition I_ex_1 : nat -> bool := 
fun n => match n with
| 0 => true
| 1 => false
| _ => false
end.

(********* EXEMPLES D'EVALUATIONS ******************)
Goal forall V, forall I, @eval V TruePL I = true.
intros.
reflexivity.
Qed.

Goal eval pl_ex_1 I_false = true.
reflexivity.
Qed.

Goal eval pl_ex_1 I_true = true.
reflexivity.
Qed.

Goal eval pl_ex_1 I_ex_1 = false.
reflexivity.
Qed.


(********* EXEMPLES DE LISTES DE VARIABLES ******************)

Goal vars pl_ex_1 = [0;1].
reflexivity.
Qed.

Goal (@vars nat) (AndPL TruePL FalsePL) = [].
reflexivity.
Qed.

(* Attention, on a des listes, pas des variables, donc l'ordre et la multiplicité compte ! *)
Goal vars pl_ex_1 <> [1;0;1].
intros H.
cbn in H.
discriminate.
Qed.


(******************************************************************************)
(* PARTIE E. PREUVE FORMELLE DU CC1 2018-2019                                 *)
(******************************************************************************)
Section CC1.
(* Le type des arbres '2 et 3' dans le CC1 2018-2019 *)

Inductive A_2_3 : Type :=
| fe_A_2_3 : A_2_3                                      (* feuille *)
| nb_A_2_3 (a1:A_2_3) (a2:A_2_3) : A_2_3                (* arbre à deux fils *)
| nt_A_2_3 (a1:A_2_3) (a2:A_2_3) (a3:A_2_3) : A_2_3.    (* arbre à trois fils *)

Definition un_arbre_2_3 : A_2_3 :=
 nt_A_2_3 (nb_A_2_3 fe_A_2_3 fe_A_2_3) (nb_A_2_3 fe_A_2_3 fe_A_2_3) (nb_A_2_3 fe_A_2_3 fe_A_2_3).
 
(* EXERCICE : dessiner "un_arbre_2_3" *)

(* Comptage des noeuds de type nb_A_2_3 *)
Fixpoint nbNB (a:A_2_3) : nat :=
match a with
 | fe_A_2_3           => 0
 | nb_A_2_3 a1 a2     => 1 + nbNB a1 + nbNB a2 
 | nt_A_2_3 a1 a2 a3  => nbNB a1 + nbNB a2 + nbNB a3
end.

Goal (nbNB fe_A_2_3) = 0.
reflexivity.
Qed.

Goal (nbNB un_arbre_2_3) = 3.
reflexivity.
Qed.

(* Comptage des noeuds de type nt_A_2_3 *)
Fixpoint nbNT (a:A_2_3) : nat :=
match a with
 | fe_A_2_3           => 0
 | nb_A_2_3 a1 a2     => nbNT a1 + nbNT a2 
 | nt_A_2_3 a1 a2 a3  => 1 + nbNT a1 + nbNT a2 + nbNT a3
end.

Goal (nbNT fe_A_2_3) = 0.
reflexivity.
Qed.

Goal (nbNT un_arbre_2_3) = 1.
reflexivity.
Qed.

(********************************)
(* EXERCICE : DEFINIR LA FONCTION "nbFE" qui compte le nombre de feuilles *)
(* REMARQUE : on a donné une définition par défaut, "0" QU'IL FAUT REMPLACER *)
(********************************)
Fixpoint nbFE (a:A_2_3) : nat :=
0.

Goal (nbFE fe_A_2_3) = 1.
reflexivity.
Qed.

Goal (nbFE un_arbre_2_3) = 6.
reflexivity.
Qed.

(* Dans la suite, on utilisera la tactique "ring" pour automatiser de fastitidueuses
   réécritures arithmétiques *)
Example reecriture_avec_ring : forall m n p, (m + n) + (p + 1) = 1 + p + (m + 0) + n.
Proof.
intros m n p.
Search (_ + 0).
rewrite Nat.add_0_r.
Search (_ + _ = _ + _).
rewrite Nat.add_comm.
(* maintenant il faut appliquer la commutativé de l'addition sur le sous-terme "(p + 1)"
   on précise les arguments pour que la réécriture ne soit pas juste l'annulation de la précédente *)
rewrite (Nat.add_comm p 1).
Search (_ + _ + _ ).
rewrite Nat.add_assoc.
trivial.
Restart.
intros.
(* c'est assez pénible, mais la tactique "ring" sait faire tout ça automatiquement *)
ring.
Qed.

(********************************)
(* EXERCICE : Prouver que pour tout "a" "(nbFE a) = 1 + (nbNB a) + 2 * (nbNT a)"
   HINT : utiliser "ring" *)
(********************************)
Lemma feuilles_noeuds_2_3 : forall a:A_2_3, (nbFE a) = 1 + (nbNB a) + 2 * (nbNT a).
Proof.
Admitted.

End CC1.

(******************************************************************************)
(* PARTIE F FACULTATIVE. LOGIQUE PROPOSITIONNELLE : SYSTEME FONCTIONNELLEMENT COMPLET    *)
(******************************************************************************)
Section LogiquePropFun.

(********************************)
(* EXERCICE : définir la fonction "pas_de_ou" qui est vraie ssi une formule "F" 
   n'utilise pas le connecteur "OrPL" *)
(* REMARQUE : on a donné une définition par défaut, "True" QU'IL FAUT REMPLACER *)
(********************************)

Fixpoint pas_de_ou {V:Set} (F : @PL V) : Prop :=
True.

(********************************)
(* EXERCICE : définir la fonction "supprime_ou" qui remplace toutes les
   occurences de "OrPL F1 F2" par une formule logiquement équivalente qui n'utilise
   pas le connecteur "OrPL" *)
(* REMARQUE : on a donné une définition par défaut, "TruePL" QU'IL FAUT REMPLACER *)
(********************************)

Fixpoint supprime_ou {V:Set} (F : @PL V) : @PL V :=
TruePL.

(********************************)
(* EXERCICE : montrer que "supprime_ou" transforme une formule "F" en "F'" qui
   ne contient pas de "OrPL" et qui est éqquivalente à "F" *)
(* HINT : vous avez déjà prouvé un lemme sur le seul cas intéressant *)
(********************************)

Lemma supprime_ou_pas_de_ou {V:Set} : forall (F : @PL V), pas_de_ou (supprime_ou F).
Proof.
Admitted.

Lemma supprime_ou_equiv {V:Set} : forall (F : @PL V), (supprime_ou F) <=> F.
Proof.
Admitted.


End LogiquePropFun.



(******************************************************************************)
(* PARTIE G FACULTATIVE. AUTOMATISATION   *)
(* /!\ ATTENTION : A PARTIR D'ICI, C'EST DU HORS PISTE /!\ *)
(******************************************************************************)

(* On montre deux petits lemmes *)

Lemma OrPL_assoc {V:Set} : forall (F1 F2 F3:@PL V), (OrPL (OrPL F1 F2) F3) <=> (OrPL F1 (OrPL F2 F3)).
Proof.
unfold equiv_PL. intros F1 F2 F3 I. cbn.
destruct (eval F1 I), (eval F2 I); reflexivity.
Qed.

Lemma AndPL_comm {V:Set} : forall (F1 F2:@PL V), (AndPL F1 F2) <=> (AndPL F2 F1).
Proof.
unfold equiv_PL. intros F1 F2 I. cbn.
destruct (eval F1 I), (eval F2 I); reflexivity.
Qed.

(********************************)
(* On voit le motif : on analyse chacun des cas possibles, on va l'automatiser *)
(********************************)

(* La tactique "destruct_eval" va détruire toutes les hypothèses de la forme "eval ?F ?I"
   et essayer de conclure. Elle va ainsi essayer de prouver l'équivalence de deux
   formules en calculant leurs tables de vérité et en les comparant ligne à ligne *)

Ltac destruct_eval' :=
 match goal with
  | [ |-  context [eval ?F ?I] ] => destruct (eval F I)
 end.

Ltac destruct_eval :=
unfold equiv_PL; intros; cbn; repeat progress destruct_eval'; auto.

(* Un exemple *)
Goal forall V (F1 F2:@PL V), (NotPL (OrPL F1 F2)) <=> ((AndPL (NotPL F1) (NotPL F2))). 
destruct_eval.
Qed.



Require Import Coq.Setoids.Setoid.

Print equiv_PL.
(* equiv_PL {V:Set} (F1 F2 : PL) : Prop := ∀ I, (@eval V) F1 I = (@eval V) F2 I. *)

(* Coq sait réécrire les relations d'équivalence, on lui dit donc que "equiv_PL" en est une *)
(* Ne vous inquiétez pas de la syntaxe, assez effrayante il faut dire *)
Add Parametric Relation {V:Set} : (@PL V) (@equiv_PL V)
  reflexivity proved by equiv_PL_refl
  symmetry proved by equiv_PL_sym
  transitivity proved by equiv_PL_trans
  as equiv_PL_rel.

(* Ensuite, on va dire à Coq que les constructeurs de "PL" respectent cette équivalence *)
(* Pour cela, on automatise un peu car les 3 preuves suivantes sont similaires *)
Ltac equiv_PL_mor' :=
repeat match goal with
  | [ H : ?F1 <=> ?F2  |-  _ ] => rewrite H
 end.
Ltac equiv_PL_mor := intros; unfold equiv_PL; intros ; cbn; equiv_PL_mor'; reflexivity.

(* Ne vous inquiétez pas de la syntaxe*)
Add Parametric Morphism {V:Set} : (@AndPL V)
  with signature (@equiv_PL V) ==> (@equiv_PL V) ==> (@equiv_PL V) as AndPL_mor.
Proof.
equiv_PL_mor.
Qed.

Add Parametric Morphism {V:Set} : (@OrPL V)
  with signature (@equiv_PL V) ==> (@equiv_PL V) ==> (@equiv_PL V) as OrPL_mor.
Proof.
equiv_PL_mor.
Qed.

Add Parametric Morphism {V:Set} : (@NotPL V)
  with signature (@equiv_PL V) ==> (@equiv_PL V) as NotPL_mor.
Proof.
equiv_PL_mor.
Qed.

(* Et ainsi on peut remplacer une formule par une autre equivalente avec "rewrite" *)
Goal forall (V:Set) (F1 F2:@PL V), NotPL (OrPL (AndPL F1 TruePL) (AndPL F1 TruePL)) <=> NotPL F1.
Proof.
intros.
assert (AndPL F1 TruePL <=> F1) as H0 by destruct_eval.
assert (OrPL F1 F1 <=> F1)  as H1 by destruct_eval.
rewrite H0, H1; reflexivity.
Restart.
(* Bon, dans ce cas là, on a notre tactique "destruct_eval" qui le ferait directement
   mais dans la partie H, on va s'en servir !*)
destruct_eval.
Qed.



(******************************************************************************)
(* PARTIE H FACULTATIVE. LEMME DE SUBSTITUTION    *)
(* /!\ ATTENTION : C'EST TOUJOURS DU HORS PISTE /!\ *)
(******************************************************************************)
Section LogiquePropSubst.

Context {V:Set}.

(* On définit une notion de substitution sur les variables propositionnelles *)
Fixpoint subst (s:V -> @PL V) (t:@PL V): @PL V :=
match t with
 | VarPL v    => s v
 | TruePL     => TruePL
 | FalsePL    => FalsePL
 | NotPL A    => NotPL (subst s A)
 | OrPL A B   => OrPL (subst s A) (subst s B)
 | AndPL A B  => AndPL (subst s A) (subst s B)
end.


(********************************)
(* EXERCICE : prouver le lemme qui lie évaluation et substitution *)
(********************************)
Lemma subst_eval : forall (A : @PL V) (s:V -> @PL V) (I: V -> bool), 
                   eval (subst s A) I = eval A (fun v => eval (s v) I).
Proof.
Admitted.


(********************************)
(* EXERCICE : prouver le principe de substitution *)
(* HINT : utiliser "subst_eval" *)
(********************************)
Theorem substitution_principle_1 : forall (A B : @PL V) (s:V -> @PL V),
        A <=> B -> (subst s A) <=> (subst s B).
Proof.
Admitted.


Context (V_eq_dec : forall (x y : V), {x = y} + {x <> y}).
(* "V_eq_dec" est l'égalité décidable sur "V" : le type est surprenant
   c'est un "sumbool : Prop → Prop → Set" c'est la façon standard de dire en Coq
   que l'égalité est décidable sur un type.
   
   En effet, la définition de "sumbool" est la suivante
   "Inductive sumbool (A B : Prop) : Set :=  
     | left : A → {A} + {B} 
     | right : B → {A} + {B}"

  Un élément de "{A} + {B}" est donc
   - (left) une preuve que "A"
   - (right) une preuve que "B"

  Mais comme le type "{A} + {B}" est dans "Set", cela veut dire qu'on peut pattern matcher
  (en oubliant la preuve) : pour les calculs, on veut juste savoir si c'est "left" ou "right".
  Donc finalement, "{A} + {B}" c'est un peu comme un booléen qui dit 'j'ai une preuve que OUI ou que NON'
*)


(* Un substitution identité partout sauf en "v", c'est là que sert "V_eq_dec"
   et son type mystérieux "{x = y} + {x <> y}" : on pattern match, simplement
   pour savoir si "v = x" ou si "x <> y" *)
Definition single_subst (v:V) (F:@PL V) : V -> @PL V :=
fun x => match (V_eq_dec v x) with 
 | left _  => F
 | right _ => VarPL x
end.

(* On reprend la notation du cours *)
Notation "[ v := F ]" := (single_subst v F).

(********************************)
(* EXERCICE : prouver le second principe de substitution *)
(* HINT : utiliser "rewrite" *)
Theorem substitution_principle_2 : forall (F A B : @PL V) (v:V),
   A <=> B -> (subst [v := A] F) <=> (subst [v := B] F).
Proof.
Admitted.

End LogiquePropSubst.







