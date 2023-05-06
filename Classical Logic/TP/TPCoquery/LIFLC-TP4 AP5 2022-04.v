(***************************** LIFLC - TP4 ************************************)
(**********                                                 *******************)
(******************************************************************************)

(*

  On reprend dans LIFLC-TP4 les fonctions qu'on a écrites en LF afin
  d'en modéliser le comportement souhaité et de prouver qu'elles le
  respectent.

*)

Require Export List.
Import ListNotations.


(******************************************************************************)
(* Rappel des fonctions codées en LF                                          *)
(******************************************************************************)


(* On définit un petit alphabet d'exemple : c'est juste une énumération, représentée
   en Coq par un type inductif avec 2 constructeurs sans argument (des constantes). *)
Inductive Alphabet : Type :=
| a : Alphabet
| b : Alphabet.

(* Ici, Alphabet est 'le plus petit ensemble qui contient a, b et rien d'autre', donc
   moralement, Alphabet est l'ensemble {a,b} *)

(* Une fonction qui teste si deux éléments de l'alphabet sont égaux *)
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

(* Tests unitaires
   Ici, la 'preuve' est obtenue par calcul : la tactique "reflexivity" fait le job. *)
Example comp_alphabet_ex1 : comp_alphabet a a = true.
Proof.
simpl.
reflexivity.
Qed.

Example comp_alphabet_ex2 : comp_alphabet a b = false.
Proof.
simpl.
reflexivity.
Qed.


(* On a vu que (comp_alphabet x y) = true si et seulement si (x = y).
   On a utilisé pour cela les tactiques vues dans les TP précédents
   - intros [Id1] [Id2] ...
   - destruct [Hypothèse]
   - discriminate
   - reflexivity
   - simpl (in [Hypothèse])
   - apply [Théorème] (in [Hypothèse])
   - rewrite [Théorème d'égalité] (in [Hypothèse]) *)
Lemma comp_alphabet_correct : forall x y, comp_alphabet x y = true -> x = y.
Proof.
 intros x y.
  - intro Hcomptrue.
   destruct x.
   + destruct y.
     * reflexivity.
     * simpl in Hcomptrue. discriminate Hcomptrue.
   + destruct y.
     * simpl in Hcomptrue. discriminate Hcomptrue.
     * reflexivity.
 Qed.

Lemma comp_alphabet_complet : forall x y, x = y -> comp_alphabet x y = true.
Proof.
 intros x y.
  - intro Hxy.
   destruct x.
    + destruct y.
      * simpl. reflexivity.
      * rewrite Hxy. simpl. reflexivity.
   + destruct y.
      * discriminate.
      * simpl. reflexivity.
Qed.


(* En particulier l'égalité sur l'alphabet est reflexive *)
(* "comp_alphabet_correct" fait exactement ce dont on a besoin, on peut donc l'utiliser *)
Lemma comp_alphabet_eq : forall x, comp_alphabet x x = true.
Proof.
intro x.
apply (comp_alphabet_complet x x).
reflexivity.
Qed.




(******************************************************************************)
(* Rappels sur le type des couples *)
(******************************************************************************)

(* Le type 'produit de A et B' est définit par "prod A B" dans la bibliothèque Coq
   Inductive prod (A B : Type) : Type := 
     pair : A -> B -> A * B

   En Coq, on écrit "A * B" au lieu de  "prod A B" (c'est juste une notation *)
Print prod.

(* Ce type n'a qu'un seul constructeur "pair" qui prend deux arguments : (x:A) et (y:B)
   Prod A B est donc 'le plus petit ensemble qui contient tous les éléments
   de la forme "pair x y" (avec x dans A et y dans B) et rien d'autre'
   donc moralement, Prod A B est le produit cartésien de A et B, qui contient
   toutes les paires (x,y) (et rien d'autre).  *)

(* Les deux fonctions qui permettent d'extraire le contenu d'une paire "(x,y)" sont
  - "fst : A * B -> A" (pour FirST)
  - "snd : A * B -> B" (pour SecoND)
 *)

Print fst.
Print snd.

(* Leur définition équivalente avec "match" : (mais avec un let caché) *)

Definition fst' A B (p:A * B) : A :=
match p with
 | (x,y) => x
end.
Print fst'.

(* Un couple d'éléments est bien le couple de ses projetés *)
(* Ce lemme nous servira plus tard *)
Lemma projection_product (A B : Type) : forall p:A*B, p = (fst p, snd p).
Proof.
intro p.
destruct p.
simpl.
reflexivity.
Qed.


(* On se donne enfin un lemme de commutation pour l'addition des nat *)
Definition plus_comm := Arith.Plus.plus_comm.
Check plus_comm.


(******************************************************************************)
(* EXERCICES ******************************************************************)
(* Listes d'entiers et plus si affinités                                      *)
(******************************************************************************)

(* On rappelle ici la définition des listes :

Inductive list (A : Type) : Type := 
  | nil : list A                     (* notation [] *)
  | cons : A -> list A -> list A     (* notation _ :: _ *)

*)

Print list.

(* on travaillera dans la première partie de ce TP avec des listes de nat : list nat *)

(* Considérons un itérateur spécialisé sur les listes d'entiers avec accumulateur
   entier.  

 foldlnat f a0 [x1;x2;x3...xn] retourne f ... (f (f (f a0 x1) x2) x3) ... xn 

   En gros : on parcourt tous les éléments de la liste en mettant à jour un 
   accumulateur (ici a0 au début) grâce à la fonction f).  

   ** C'est une forme du "reduce" que vous avez vu en lifap5 **
 *)

Fixpoint foldlnat (f : nat -> nat -> nat) (acc : nat) (l : list nat) :=
  match l with
  | [] => acc
  | h::rl => foldlnat f (f acc h) rl 
  end.


(* Considérons une fonction retournant le successeur de son premier argument *)
Definition plus_un (x : nat)  (y : nat) := S x .


(* On peut définir deux fonctions à partir de ce foldlnat... *)

Definition longueur_fold_aux := foldlnat plus_un.

Definition longueur_fold := longueur_fold_aux 0.


(* EXERCICE ******************************************************************************

   ÉNONCEZ ET PROUVEZ le fait que longueur_fold_aux x l retourne la
   somme de x et de la longueur de l.

   On appellera ce lemme aux_is_plus_x.

   HINT : On pourra avoir besoin dans la preuve d'un lemme de commutation de l'addition comme : plus_comm.

   HINT : vous pouvez ajouter une nouvelle assertion dans le contexte avec 
   la tactique "assert H", un nouveau sous-but demandant de prouver "H"
   est alors ajouté 

   HINT : Tactiques suffisantes et pas forcément nécessaires, 
     assert exact intro induction reflexivity rewrite simpl 
     unfold (éventuellement son contraire fold pour replier une définition en son nom) 
*)




(* Lemma aux_is_plus_x : *)



  
(* EXERCICE ******************************************************************************

   ÉNONCEZ ET PROUVEZ le fait que longueur_fold l retourne la
   la longueur de l.

   On appellera ce lemme longueur_fold_lenght 
*)

(* Lemma longueur_fold_length : *)


(* EXERCICE ******************************************************************************
   Soit la fonction "appartient" qui prend en paramètres
   un entier n et une liste d'entiers et renvoie true si et seulement si
   n est dans la liste *)
Fixpoint appartient (x : nat) (l : list nat) : bool :=
  match l with
  | nil   => false
  | h::rl => (Nat.eqb x h) || (appartient x rl)
  end.

(* Tests unitaires avec reflexivity *)
Example appartient_ex1 : appartient 0 [1;3;0;5] = true.
Proof.
simpl. reflexivity.
Qed.
Example appartient_ex2 : appartient 4 [1;3;0;5] = false.
Proof.
simpl. reflexivity.
Qed.

(* Cette fonction est-elle correcte ? *)

(* ÉNONCEZ ET PROUVEZ la propriété que l'appartenance d'un élément à une liste vide
   est fausse.
 
   On appellera ce lemme appartient_vide.

 *)
(* Lemma appartient_vide : *)




(* EXERCICE ******************************************************************************

   ÉNONCEZ ET PROUVEZ *le lemme de correction* de "appartient"
  nommé "appartient_correct_In" qui dit en langue naturelle :
   (appartient x ls) est vrai SEULEMENT SI le prédicat d'appartenance In de x à l est vérifié. 

  La preuve se fera par induction sur la liste puis selon le cas
  d'égalité de l'élément recherché et du premier élément de la liste. *)


(* Les lemmes de simplification du ou booléen qu'on sera peut-être amené à utiliser :  *)
Check Bool.orb_true_r. (* La simplification de x orb true en true *)
Check Bool.orb_false_r.(* La simplification de x orb false en false *)
Check Bool.orb_true_l. (* La simplification de true orb x en true *)
Check Bool.orb_false_l.(* La simplification de false orb x en x *)


(* Un petit lemme technique pour simplifier... *)
Lemma eqb_true_false : forall x y,  Nat.eqb x y = true \/ Nat.eqb x y = false.
Proof.
  intros x y.
  destruct (Nat.eqb x y). (* Notez bien : suivant le cas de Nat.eqb x y *)
  - left. reflexivity.
  - right. reflexivity. 
Qed.


(* Lemma appartient_correct_In : *)


(* EXERCICE ******************************************************************************
  ÉNONCEZ ET PROUVEZ *le lemme de complétude* de "appartient"
  nommé "appartient_complet_In" qui dit en langue naturelle :
  SI le prédicat d'appartenance In de x à l est vérifié alors (appartient x ls) est vrai 


  La preuve se fera par induction sur la liste puis selon le cas
  d'égalité de l'élément recherché et du premier élément de la liste. *)


(* On pourra avoir besoin du lemme qui dit que Nat.eqb x x s'évalue toujours à true. *)
Check PeanoNat.Nat.eqb_refl.
  
(* Lemma appartient_complet_In : *)

(*****************************************************************************************)

(* On va maintenant jouer avec UN EXISTENTIEL...

   Manipulation des existentiels :

   - DANS LE BUT, un exists demande juste de fournir un bon
     temoin. Celui-ci est fourni par l'invocation de la tactique
     "exists".
*)

Lemma exemple_exist_1 : exists (x : nat), x = 666.
  (* connaît-on un x qui satisfait ce prédicat d'égalité ? Hé bien on peut penser à... 666. *)
Proof.
  exists 666.
  reflexivity.
Qed.

(* - DANS UNE HYPOTHÈSE, un exists peut être déstructuré par destruct.
     On obtient alors en nouvelle hypothèse le témoin, sur lequel on
     ne sait rien sinon qu'il vérifie la propriété quantifiée.  *)

Lemma exemple_exist_2 : (exists (x : nat), x = 666) -> exists (y : nat), y = 667.
Proof.
  intro Hex.
  destruct Hex as [x' P].
  (* allez, pour rire... *)
  exists (S x').
  rewrite P.
  reflexivity. 
Qed.

(* EXERCICE  *********************************************************************)
(* ÉNONCEZ ET PROUVEZ *le lemme de correction* de "appartient" nommé
  "appartient_correct" qui dit en langue naturelle : (appartient x ls)
  est vrai SEULEMENT SI il existe une décomposition de ls de la forme
  ls = l1 ++ x :: l2 (donc pour le prédicat d'égalité "=" sur les listes)

  La preuve se fera par induction sur la liste puis selon le cas
d'égalité de l'élément recherché et du premier élément de la liste. *)


(* Lemma appartient_correct : *)



(* EXERCICE FACULTATIF *)
(* ÉNONCEZ ET PROUVEZ *le lemme de complétude* de "appartient"
  nommé "appartient_complet" qui dit en langue naturelle :
   SI il existe une décomposition 
   de ls de la forme ls = l1 ++ x :: l2 alors  (appartient x ls) est vrai. 

*)

(* La preuve se fera par induction sur la liste puis selon le cas
d'égalité de l'élément recherché et du premier élément de la liste.
*)

(* Lemma appartient_complet : *)



(******************************************************************************)
(* Recherche dans les listes de paires *)
(******************************************************************************)

(* on peut représenter un dictionnaire comme une liste de paire (clef, valeur) *)

(* La principale fonctionnalité qu'on attend d'un dictionnaire est de pouvoir retrouver
la valeur associée à une clef. Si plusieurs valeurs sont associées, alors on retourne la 
première qu'on trouve.

On comprend bien que rien de garantit qu'on trouve toujours une valeur, donc le type
de retour de cette fonction est de type "option valeur" *)


(* EXERCICE *******************************************************************)
(* Définir la fonction "trouve" qui prend en paramètres
    - une listes de paires (clef,valeur)
    - une clef k
   renvoie la première valeur associée à k quand elle existe et None sinon *)
(* Fixpoint trouve (assoc : list (Alphabet * nat)) (key : Alphabet) : option nat := *)

(* Tests unitaires avec reflexivity *)
Example trouve_ex1 :  trouve [(a,1); (b,2)] a = Some 1.
Proof.
simpl. reflexivity.
Qed.
Example trouve_ex2 :  trouve [(a,2); (a,1)] a = Some 2.
Proof.
simpl. reflexivity.
Qed.
Example trouve_ex3 :  trouve [(a,2); (a,1)] b = None.
Proof.
simpl. reflexivity.
Qed.


(* EXERCICE *******************************************************************)
(* ÉNONCEZ ET PROUVEZ la propriété "trouve_tete" qui exprime que pour toute liste l, toute clé k 
   et toute valeur v, trouve ((k,v)::l) k = Some v. *)

(* Lemma trouve_tete : *)



(* On se donne une fonction test d'égalité sur les couples Alphabet * nat... *)
Definition comp_pair p1 p2 := match p1 with
                              | (k,v) => match p2 with
                                       | (x,y) => andb (comp_alphabet k x) (Nat.eqb v y)
                                       end
                              end.

(* ... ainsi qu'un petit lemme technique pour simplifier des preuves. *)
Lemma comp_alphabet_true_false : forall x y, comp_alphabet x y = true \/ comp_alphabet x y = false.
Proof.
  intros x y.
  destruct  (comp_alphabet x y). (* Notez bien : suivant le cas de comp_alphabet x y *)
  - left. reflexivity.
  - right. reflexivity.
Qed.


(* EXERCICE *******************************************************************)
(* ÉNONCEZ ET PROUVEZ la propriété "trouve_correct" qui exprime que la fonction trouve appliquée 
   à une liste l et une clef k retourne Some v seulement s'il existe une décomposition de l de la forme
   l = l1 ++ (k,v) :: l2 (donc pour le prédicat d'égalité "=" sur les listes). *)


(* Lemma trouve_correct : *)


(* EXERCICE FACULTATIF ********************************************************)
(* On peut penser à montrer que c'est également complet *)

