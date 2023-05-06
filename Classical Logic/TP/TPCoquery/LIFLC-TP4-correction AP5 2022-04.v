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

(* EXERCICE *)
(* On va montrer que (comp_alphabet x y) = true si et seulement si (x = y).
   On va utiliser pour cela les tactiques vues dans les TP précédents
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


(* EXERICE *)
(* Compléter la preuve suivante
   HINT : "comp_alphabet_correct" fait exactement ce dont on a besoin, on peut donc l'utiliser *)
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

   En Coq, on écrit "A * B" au lieu de  "prod A B" (c'est juste une notation*
*)
Print prod.

(* Ce type n'a qu'un seul constructeur "pair" qui prend deux arguments : (x:A) et (y:B)
   Prod A B est donc 'le plus petit ensemble qui conteient tous les éléments
   de la forme "pair x y" (avec x dans A et y dans B) et rien d'autres'
   donc moralement, Prod A B est le produit cartésien de A et B, qui contient
   toutes les paires (x,y) (et rien d'autres).  *)

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

(* EXERCICE *)
(* Prouver le lemme suivant *)
Lemma projection_product (A B : Type) : forall p:A*B, p = (fst p, snd p).
Proof.
intro p.
destruct p.
simpl.
reflexivity.
Qed.



(******************************************************************************)
(* Listes d'entiers et plus si affinités  *)
(******************************************************************************)

(* On rappelle ici la définition des listes natives : on aurait pu
   tout faire avec les listes définies dans les TP précédents, comme
   avec nos entiers, mais c'est réinventer la roue

Inductive list (A : Type) : Type := 
  | nil : list A                     (* notation [] *)
  | cons : A -> list A -> list A     (* notation _ :: _ *)

*)

Print list.


(* Un itérateur spécialisé sur les listes d'entiers avec accumulateur
   entier.  
 foldlnat f a0 [x1;x2;x3...xn] retourne f ... (f (f (f a0 x1) x2) x3) ... xn 

   En gros : on parcourt tous les éléments de la liste en mettant à jour un 
   accumulateur (ici a0 au début) grâce à la fonction f).  

   C'est une forme du "reduce" que vous avez vu en lifap5
 *)

Fixpoint foldlnat (f : nat -> nat -> nat) (acc : nat) (l : list nat) :=
  match l with
  | [] => acc
  | h::rl => foldlnat f (f acc h) rl 
  end.


Definition plus_un (x : nat)  (y : nat) := S x .


(* On définit deux fonctions à partir de ce foldlnat *)


Definition longueur_fold_aux := foldlnat plus_un.

Definition longueur_fold := longueur_fold_aux 0.


(* EXERCICE

   Énoncez et prouvez le fait que longueur_fold_aux x l retourne la
   somme de x et de la longueur de l 

   HINT : On pourra avoir besoin dans la preuve d'un lemme de commutation de l'addition comme : plus_comm.

   HINT : vous pouvez ajouter une nouvelle assertion dans le contexte avec 
   la tactique "assert H", un nouveau sous-but demandant de prouver "H"
   est alors ajouté 

   Tactiques suffisantes et pas forcément nécessaires : 
     assert exact intro induction reflexivity rewrite simpl 
     unfold (éventuellement son contraire fold pour replier une définition en son nom) 
*)


Definition plus_comm := Arith.Plus.plus_comm.
Check plus_comm.

Lemma aux_is_plus_x : forall l x, longueur_fold_aux x l = x + length l.
Proof.
  induction l as [| h rl IHrl]. (* la tarte à la crème est ici *)
  - intro x. simpl. rewrite plus_comm. simpl. reflexivity.
  - intro x0. simpl.
    assert (Youpi :  longueur_fold_aux (S x0) rl = S x0 + length rl).
    { exact (IHrl (S x0)). } 
    rewrite plus_comm. simpl. rewrite plus_comm. (* aaah la commutation... *)
    simpl in Youpi.
    unfold longueur_fold_aux. unfold longueur_fold_aux in Youpi.
    unfold plus_un. simpl.
    fold plus_un. (* ça se voit mieux là *)
    exact Youpi.

    Restart. (* RT : variante *)
    (* Ici on recommence la preuve pour montrer une autre version, qui fait appel à pplus d'automatisation *)

    induction l as [| h rl IHrl]; intros x; auto with arith.
    cbn; rewrite IHrl; rewrite <- PeanoNat.Nat.add_succ_comm; reflexivity.
Qed.

(* EXERCICE

   Énoncez et prouvez le fait que longueur_fold l retourne la
   la longueur de l 
*)

Lemma longueur_fold_is_length : forall l, longueur_fold l = length l.
Proof.
  intro l.
  unfold longueur_fold.
  rewrite aux_is_plus_x. 
  simpl. reflexivity.
Qed.


(* EXERCICE *)
(* Définir la fonction "appartient" qui prend en paramètres
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



(* EXERCICE *)
(* Ennoncer et prouver la propriété que l'appartenance d'un élément à une liste vide
   est fausse *)
Lemma appartient_vide : forall n, appartient n [] = false.
Proof.
  intro n.
  simpl. reflexivity.
Qed.

(* EXERCICE *)
(* Ennoncer et prouver la propriété que l'appartenance d'un élément à une liste singleton
   est vraie SSI l'élément recherché et celui du singleton sont égaux
   On utilisera les théorèmes suivants
   "Bool.orb_false_r : forall b : bool, (b || false)%bool = b"
   "PeanoNat.Nat.eqb_eq : forall n m : nat, PeanoNat.Nat.eqb n m = true <-> n = m"
*)

Lemma appartient_singleton : forall x y, appartient x [y] = true <-> x = y.
Proof.
intros x y. simpl.
split; intros H.
 - (* appartient x [y] = true -> x = y *)
   rewrite Bool.orb_false_r in H.
   rewrite PeanoNat.Nat.eqb_eq in H.
   assumption.
 - rewrite Bool.orb_false_r.
   rewrite PeanoNat.Nat.eqb_eq.
   assumption.
Qed.




(* EXERCICE *)
(* Ecrire ET PROUVER *le lemme de correction* de "appartient"
  nommé "appartient_correct_In" qui dit en langue naturelle :
   (appartient x ls) est vrai SEULEMENT SI le prédicat d'appartenance In de x à l est vérifié. 


  La preuve se fera par induction sur la liste puis selon le cas
  d'égalité de l'élément recherché et du premier élément de la liste. *)


(* les lemmes de simplification du ou booléen qu'on sera peut-être amené à utiliser :  *)
Check Bool.orb_true_r.
Check Bool.orb_false_r.
Check Bool.orb_true_l.
Check Bool.orb_false_l.


(* un petit lemme technique pour simplifier... *)
Lemma eqb_true_false : forall x y,  Nat.eqb x y = true \/ Nat.eqb x y = false.
Proof.
  intros x y.
  destruct (Nat.eqb x y). (* suivant le cas de Nat.eqb x y *)
  - left. reflexivity.
  - right. reflexivity. 
Qed.


Lemma appartient_correct_In :
  forall (x : nat) (l : list nat), appartient x l = true -> In x l.
Proof.
intros x l.
induction l as [| hl rl IHrl].
- intro app_vide. exfalso. (* exfalso pour clarifier *)
  simpl in app_vide.
  discriminate.
- simpl.
  destruct (eqb_true_false x hl) as [Heqb_true | Heqb_false].
  +  apply PeanoNat.Nat.eqb_eq in Heqb_true.
     rewrite Heqb_true.
     intro dummy. clear dummy. (* on s'en sert pas hein ? *)
     left. reflexivity.
  +  rewrite Heqb_false.
     rewrite Bool.orb_false_l.
     intro Happ_true.     
     right.
     apply IHrl.
     exact Happ_true.
     
Restart. (* RT : variante *)
(* On recommence la preuve pour montrer une autre version, plus automatisée. *)     
induction l as [| hl rl IHrl]; cbn; intros H; try discriminate.
rewrite Bool.orb_true_iff in H; destruct H.
 - left; rewrite PeanoNat.Nat.eqb_eq in H; auto.
 - right; auto.
Qed.

(* EXERCICE *)
(* Ecrire ET PROUVER *le lemme de complétude* de "appartient"
  nommé "appartient_complet_In" qui dit en langue naturelle :
  SI le prédicat d'appartenance In de x à l est vérifié alors (appartient x ls) est vrai 


  La preuve se fera par induction sur la liste puis selon le cas
  d'égalité de l'élément recherché et du premier élément de la liste. *)


(* on pourra avoir besoin du lemme qui dit que Nat.eqb x x s'évalue toujours à true. *)
Check PeanoNat.Nat.eqb_refl.
  
Lemma appartient_complet_In : forall (x : nat) (l : list nat),
    In x l -> appartient x l = true.
Proof.
  intros x l.
  induction l as [| hl rl IHrl].
  - intro absurde. exfalso. (* exfalse pour clarifier *)
    simpl in absurde.
    exact absurde.
  - simpl. intro H_In.
    destruct (eqb_true_false x hl) as [Heqb_true | Heqb_false].
    + rewrite Heqb_true.
      rewrite Bool.orb_true_l. reflexivity.
    + rewrite Heqb_false.
      rewrite Bool.orb_false_l.
      destruct H_In as [Hhx | H_In_rl].
      * exfalso.
        rewrite Hhx in Heqb_false.
        rewrite PeanoNat.Nat.eqb_refl in Heqb_false. discriminate.
      * exact (IHrl H_In_rl).
        
Restart. (* RT : variante *)
(* On recommence la preuve pour montrer une autre version, plus automatisée. *) 
induction l as [| hl rl IHrl]; cbn; intros H; try contradiction.
rewrite Bool.orb_true_iff; destruct H; [left | right]; auto.
rewrite PeanoNat.Nat.eqb_eq; auto.
Qed.

(* On montre le lien avec la lib std *)
Definition sumbool_to_bool {A} {B} : {A} + {B} -> bool :=
  fun x => match x with
    | left _ => true
    | right _ => false
    end.
    
Definition appartient' (n : nat) (ls : list nat) : bool :=
sumbool_to_bool (in_dec (PeanoNat.Nat.eq_dec) n ls).

Lemma appartient'_correct : forall (x : nat) (l : list nat), appartient' x l = true <-> In x l.
Proof.
unfold appartient', sumbool_to_bool.
intros x l.
destruct (in_dec PeanoNat.Nat.eq_dec x l); split; auto; discriminate.
Qed.


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

(* EXERCICE  *)
(* Écrire ET PROUVER *le lemme de correction* de "appartient" nommé
  "appartient_correct" qui dit en langue naturelle : (appartient x ls)
  est vrai SEULEMENT SI il existe une décomposition de ls de la forme
  ls = l1 ++ x :: l2 (donc pour le prédicat d'égalité "=" sur les listes)

  La preuve se fera par induction sur la liste puis selon le cas
d'égalité de l'élément recherché et du premier élément de la liste. *)


Lemma appartient_correct : forall (x : nat) (l : list nat),
                           appartient x l = true -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
intros x l.
induction l as [| hl rl IHrl].
- intro absurde.
  simpl in absurde.
  discriminate.
- simpl.
  destruct (eqb_true_false x hl) as [Heqb_true | Heqb_false].
  +  apply PeanoNat.Nat.eqb_eq in Heqb_true. rewrite Heqb_true.
     intro dummy. clear dummy.
     exists [].  exists rl.
     simpl.  reflexivity.
  +  rewrite Heqb_false.
     rewrite Bool.orb_false_l.
     intro Happ_true.     
     apply IHrl in Happ_true.
     destruct Happ_true as [l1' Hex_rl].
     destruct (Hex_rl) as [l2' Hrl].
     rewrite Hrl.
     exists (hl::l1').
     exists l2'.
     simpl. reflexivity.
Qed.

(* EXERCICE FACULTATIF *)
(* Ecrire ET PROUVER *le lemme de complétude* de "appartient"
  nommé "appartient_complet" qui dit en langue naturelle :
   SI il existe une décomposition 
   de ls de la forme ls = l1 ++ x :: l2 alors  (appartient x ls) est vrai. 

*)

(* La preuve se fera par induction sur la liste puis selon le cas
d'égalité de l'élément recherché et du premier élément de la liste.
*)

Lemma appartient_complet : forall (x : nat) (l : list nat),
    exists l1 l2, l = l1 ++ x :: l2 -> appartient x l = true.
Proof.
  intros x l.
  induction l as [| hl rl IHrl].
  - exists [].
    exists [].
    simpl.
    intro absurde.
    discriminate.
  - simpl.
    destruct (eqb_true_false x hl) as [Heqb_true | Heqb_false].
    + rewrite Heqb_true.
      rewrite Bool.orb_true_l.
      exists []. exists []. intro dummy. clear dummy. reflexivity.
    + rewrite Heqb_false.
      rewrite Bool.orb_false_l.
      destruct IHrl as [l1' Hrl_l2].
      destruct Hrl_l2 as [l2' Hrl].
      exists (hl::l1').
      exists l2'.
      simpl.
      intro H_sous_hl.
      injection H_sous_hl. exact Hrl.
Qed.





(******************************************************************************)
(* Recherche dans les listes de paires *)
(******************************************************************************)

(* on peut représenter un dictionnaire comme une liste de paire (clef, valeur) *)

(* La principale fonctionalité que l'on attend d'un dictionnaire est de pouvoir retrouver
la valeur associée à une clef. Si plusieurs valeurs sont associées, alors on retourne la 
première qu'on trouve.

On comprend bien que rien de garantit qu'on trouve toujours une valeur, donc le type
de retour de cette fonction est de type "option valeur" *)


(* EXERCICE *)
(* Définir la fonction "trouve" qui prend en paramètres
    - une listes de paires (clef,valeur)
    - une clef k
   renvoie la première valeur associée à k quand elle existe et None sinon *)
Fixpoint trouve (assoc : list (Alphabet * nat)) (key : Alphabet) : option nat :=
  match assoc with
    | nil => None
    | h::rassoc => if (comp_alphabet key (fst h)) then (Some (snd h))
                   else trouve rassoc key
  end.


Check trouve.
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


(* EXERCICE *)
(* Enoncer et prouver la propriété "trouve_tete" qui, pour toute liste l, toute clé k et toute valeur v,
   trouve ((k,v)::l) k = Some v. *)
(* HINT : vous pouvez ajouter une nouvelle assertion dans le contexte avec 
   la tactique "assert H", un nouveau sous-but demandant de prouver "H"
   est alors ajouté *)
Lemma trouve_tete : forall k v l, trouve ((k,v)::l) k = Some v.
Proof.
intros.
simpl.
assert (comp_alphabet k k = true). { exact (comp_alphabet_eq k). }
destruct (comp_alphabet k k).
- reflexivity.
- discriminate.
Qed.



Definition comp_pair p1 p2 := match p1 with
                              | (k,v) => match p2 with
                                       | (x,y) => andb (comp_alphabet k x) (Nat.eqb v y)
                                       end
                              end.

(* un petit lemme technique pour simplifier *)
Lemma comp_alphabet_true_false : forall x y, comp_alphabet x y = true \/ comp_alphabet x y = false.
Proof.
  intros x y.
  destruct  (comp_alphabet x y).
  - left. reflexivity.
  - right. reflexivity.
Qed.



Lemma trouve_correct : forall k v l, trouve l k = Some v -> existsb (comp_pair (k,v)) l = true.
Proof.
  intros k v l Htrouve.
  induction l as [| h rl IHrl].
  - simpl in Htrouve. discriminate.
  - destruct (comp_alphabet_true_false k (fst h)) as [Hktrue|Hkfalse].
    + destruct (eqb_true_false v (snd h)) as [Hvtrue|Hvfalse].
      * simpl.
        apply comp_alphabet_correct in Hktrue.
        rewrite PeanoNat.Nat.eqb_eq in Hvtrue.
        assert (Hh : h = (k,v)).
        { rewrite Hvtrue. rewrite Hktrue. apply projection_product. }
        rewrite Hh.
        rewrite comp_alphabet_eq.
        rewrite PeanoNat.Nat.eqb_refl.  
        simpl. reflexivity.
      * exfalso.                        (* pour clarifier *)
        unfold trouve in Htrouve.
        rewrite Hktrue in Htrouve.
        injection Htrouve.
        intro Hhv.
        rewrite Hhv in Hvfalse.
        rewrite PeanoNat.Nat.eqb_refl in Hvfalse. discriminate.
    + simpl.
      rewrite Bool.orb_true_iff. 
      right.
      apply IHrl.
      simpl in Htrouve.
      rewrite Hkfalse in Htrouve.
      exact Htrouve.
Qed.

Lemma trouve_correct_concat : forall k v l, trouve l k = Some v -> exists l1 l2, l = l1 ++ (k,v) :: l2.
Proof.
intros k v  l.
induction l as [| h rl IHrl].
- intro trouve_vide.
  simpl in trouve_vide.
  discriminate.
- simpl.
  assert (Hk : comp_alphabet k (fst h) = true \/ comp_alphabet k (fst h) = false).
  { destruct  (comp_alphabet k (fst h)).
    left. reflexivity. right. reflexivity. } (* faire un lemme pour ca *)
  destruct Hk as [Hktrue | Hkfalse].
  + rewrite Hktrue.
    intro Hhv_some.
    injection Hhv_some. intro Hhv.
    apply comp_alphabet_correct in Hktrue. 
    assert (Hh : h = (k,v)).
    { rewrite Hktrue. rewrite <- Hhv. apply projection_product. }
    rewrite Hh.
    exists []. exists rl. simpl. reflexivity.
  + rewrite Hkfalse.
    intro Htrouve_true.
    destruct (IHrl Htrouve_true) as [l1' Hex_rl].
    destruct (Hex_rl) as [l2' Hrl].
    rewrite Hrl. 
    exists (h::l1'). exists l2'. simpl. reflexivity.
Qed.



(* une version sans let caché *)
Definition comp_pair' p1 p2 := andb (comp_alphabet (fst p1) (fst p2)) (Nat.eqb (snd p1) (snd p2)).


Lemma trouve_correct' : forall k v l, trouve l k = Some v -> existsb (comp_pair' (k,v)) l = true.
  intros k v l Htrouve.
  induction l as [| h rl IHrl].
  - simpl in Htrouve. discriminate.
  - assert (Hk : comp_alphabet k (fst h) = true \/ comp_alphabet k (fst h) = false).
    { destruct  (comp_alphabet k (fst h)).
      left. reflexivity. right. reflexivity. } (* faire un lemme pour ca *)
    assert (Hv : Nat.eqb v (snd h) = true \/ Nat.eqb v (snd h) = false).
    { destruct  (Nat.eqb v (snd h)).
      left. reflexivity. right. reflexivity. } (* faire un lemme pour ca *)
    destruct Hk as [Hktrue|Hkfalse].
    + destruct Hv as [Hvtrue|Hvfalse].
      * simpl.
        apply comp_alphabet_correct in Hktrue.
        rewrite PeanoNat.Nat.eqb_eq in Hvtrue.
        assert (Hh : h = (k,v)).
        { rewrite Hktrue. rewrite Hvtrue. apply projection_product. }
        rewrite Hh.
        unfold comp_pair'. simpl.
        rewrite comp_alphabet_eq.
        rewrite PeanoNat.Nat.eqb_refl.  (* indiquer dans énoncé *)
        simpl. reflexivity.
      * exfalso.                        (* pour clarifier *)
        unfold trouve in Htrouve.
        rewrite Hktrue in Htrouve.
        injection Htrouve.
        intro Hhv.
        rewrite Hhv in Hvfalse.
        rewrite PeanoNat.Nat.eqb_refl in Hvfalse. discriminate.
    + simpl.
      rewrite Bool.orb_true_iff. (* indiquer dans énoncé *)
      right.
      apply IHrl.
      unfold trouve in Htrouve.
      rewrite Hkfalse in Htrouve.
      fold trouve in Htrouve. assumption. (* ici le fold n'est pas nécessaire *)
Qed.
      
(* on peut penser à montrer que c'est également complet *)


     (* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)
      
(******************************************************************************)
(* Partie E : la représentation des Automates en Coq  *)
(******************************************************************************)

(* Formellement, dans le cours de LIFLF, un Automate est un quintuplet
      <Sigma, K, i, F, delta : K*Sigma -> K >
   avec 
   - Sigma l'alphabet,
   - K l'ensemble des états,
   - i l'état initial,
   - F l'ensemble des état finaux
   - delta la fonction de transition
*)

(* Ici, on va représenter les ensembles par des listes et la fonction de transition par une fonction (!).
   On va s'appuyer sur le type "Alphabet" défini au début du sujet. De même, on va prendre les
   entiers "nat" pour identifier les états.
*)

(* EXERCICE *)
(* Définir le type Automate représentant ce quintuplet. *)
  Inductive Automate : Type :=
    automate : list Alphabet -> list nat -> nat -> list nat -> (Alphabet  -> nat -> option nat) -> Automate.

(* Pour un automate a défini par "automate Sigma K i F delta", le parallèle avec 
   le quintuplet <Sigma, K, i, F, delta> du cours.
   On justifie la réprésentation et le choix des types :
    - l'alphabet Sigma est la liste des symboles utilisés
    - (K:list nat) c'est *la liste* de TOUS les états. Une liste c'est différent d'un ensemble, plus facilement programmable
    - (i:nat) c'est clair
    - (F:list nat) une liste de nat des états finals. Là encore ensemble <> liste. 

    La principale différence est sur le choix de la fonction
    de transition delta (delta: Alphabet -> nat -> option nat)

    C'est *presque* le type usuel K*Sigma -> K 'au swap et à la curryfication près' 
    ET avec une "option" sur le résultat. "option" permet d'exprimer que la fonction
    de transition delta est *partielle* (et non totale) : on va en fait manipuler
    en Coq des automates aux transitions *partielles*.

    Ça ne change rien au fond, mais c'est plus pratique à programmer.
 *)

(* Question : pour un automate "A = automate Sigma Q i F delta", peut-on
              dire que les élements de F qui ne sont pas dans Q
              sont insignifiants ? *)

(* EXERCICE FACULTATIF *)
(* On définit l'ensemble des automates *partiels* comme ceux dont la fonction de transition delta est partielle.
              'Ca ne change rien au fond' : le prouver.
  HINT : ajouter un état puit
  REMARQUE : le rédacteur verrait bien cette question en examen.
*)


(* EXERCICE *)
(* Définir les 4 fonctions suivantes *)

(* etats : prend en paramètre un automate et renvoie la liste des états *)
Definition etats  (a : Automate) :  list nat :=
  match a with
    automate _ ql _  _ _ => ql
  end.

(* initial : prend en paramètre un automate et renvoie l'état initial *)
Definition initial  (a : Automate) :  nat :=
  match a with
    automate _ _ q0 _ _ => q0
  end.

(* acceptant : prend en paramètre un automate et un état et renvoie "true" SSI q est un état final *)
Definition acceptant  (a : Automate) (q : nat) : bool  :=
  match a with
    automate _ _ _ lF _ => (appartient q lF)
  end.

(* transition : prend en paramètre un automate, un état et un symbole, et renvoie l'état (optionnellement)
   accessible depuis "q" en lisant "c" *)
Definition transition  (a : Automate) (q : nat) (c : Alphabet) : option nat :=
  match a with
    automate _ _ _ _ f => f c q
  end.


(* EXERCICE *)
(* Exemple : définir l'automate à deux états qui accepte les mots contenant un nombre impair de 'b',
             et donner des tests unitaires *)

Definition delta_ex := fun c q =>
match (c,q) with
 | (a,1) => Some 1 
 | (b,1) => Some 2 
 | (a,2) => Some 2 
 | (b,2) => Some 1
 | (_,_) => None
end.

Definition auto_ex := automate [a;b] [1;2] 1 [2] (delta_ex).

Example auto_ex_etats : etats auto_ex = [1;2].
Proof.
simpl. reflexivity.
Qed.
Example auto_ex_initial : initial auto_ex = 1.
Proof.
simpl. reflexivity.
Qed.
Example auto_ex_acceptant_1 : acceptant auto_ex 1 = false.
Proof.
simpl. reflexivity.
Qed.
Example auto_ex_acceptant_2 : acceptant auto_ex 2 = true.
Proof.
simpl. reflexivity.
Qed.
Example auto_ex_transition_1 : transition auto_ex 1 a = Some 1.
Proof.
simpl. reflexivity.
Qed.
Example auto_ex_transition_2 : transition auto_ex 2 b = Some 1.
Proof.
simpl. reflexivity.
Qed.


(* EXERCICE *)
(* Définir "execute" qui va calculer l'état d'arrivée en lisant un mot, c'est-à-dire une "list Alphabet" *)

Fixpoint execute  (a : Automate)  (q : nat) (m : list Alphabet) : option nat :=
  match m with
  | nil => Some q
  | h::rm => match transition a q h with
             | None => None
             | Some e => execute a e rm end
  end.

Example auto_ex_execute_1 : execute auto_ex 1 [] = Some 1.
simpl. reflexivity. Qed.
Example auto_ex_execute_2 : execute auto_ex 1 [a;a;b;a;b;b] = Some 2.
simpl. reflexivity. Qed.


(* EXERCICE *)
(* Définir "reconnait" qui va accepter ou refuser un mot *)

Definition reconnait (a : Automate) (m : list Alphabet) : bool :=
  match (execute a (initial a) m) with
  | None => false
  | Some e => acceptant a e
  end.

Example auto_ex_reconnait_1 : reconnait auto_ex [] = false.
reflexivity. Qed.
Example auto_ex_reconnait_2 : reconnait auto_ex [a;a;b;a;b;b] = true.
reflexivity. Qed.



(******************************************************************************)
(* Partie F : la représentation des fonctions de transition en Coq ou 
              recherche dans les listes de paires  *)
(******************************************************************************)


(* On a très envie de pouvoir donner une description de la fonction de
   transition par SON GRAPHE (rappel, le graphe d'une fonction f : A -> B est
    la relation définie par { (x,f(x)) | x dans A}) plutôt que donner son code.
*)

Print delta_ex.
(*
Definition delta_ex := fun c q =>
match (c,q) with
 | (a,1) => Some 1 
 | (b,1) => Some 2 
 | (a,2) => Some 2 
 | (b,2) => Some 1
 | (_,_) => None
end.
*)

(* Comme le domaine de la fonction de transition est fini, on peut faire l'inverse,
   c'est-à-dire construire une fonction à partir d'un graphe FINI.

   On va représenter le graphe de f par *un dictionnaire*, une liste de paires (clef, valeur).

   La principale fonctionalité que l'on attend d'un dictionnaire est de pouvoir retrouver
   la valeur associée à une clef. En le faisant, on reconstruit (à un "option" près) f
*)


Check trouve.

(* On voit bien qu'en fixant le premier paramètre on a une fonction *partielle*
   de Alphabet dans nat *)
Check (trouve [(a,1); (b,2)] : Alphabet -> option nat).



(* On a presque tous les ingrédients pour construire une fonction de transition
   à partir de son graphe *)


(* EXERCICE *)
(* Définir la fonction "trouve2" avec pour type
              "list (nat * list (alphabet * nat)) -> nat -> option list (alphabet * nat)" *)
Fixpoint trouve2 (assoc : list (nat * list (Alphabet * nat))) (key : nat) : option (list (Alphabet * nat)) :=
  match assoc with
    | nil => None
    | h::rassoc => if (Nat.eqb key (fst h)) then (Some (snd h))
                   else trouve2 rassoc key
  end.

(* EXERCICE *)
(* En utilisant "trouve" et "trouve2", définir une fonction "graphe_vers_fonction" qui transforme
   une liste "list (nat * list (Alphabet * nat))" en une fonction "Alphabet -> nat -> option nat" *)
Definition graphe_vers_fonction (assoc : list (nat * list (Alphabet * nat))) : Alphabet -> nat -> option nat :=
  fun c q => 
     match (trouve2 assoc q) with 
     | None => None
     | Some assoc => trouve assoc c
     end.


Print delta_ex.
(* Definition delta_ex := fun c q =>
match (c,q) with
 | (a,1) => Some 1 
 | (b,1) => Some 2 
 | (a,2) => Some 2 
 | (b,2) => Some 1
 | (_,_) => None
end.
 *)

(* On est au bout (enfin !)  *)

Definition delta_ex_graphe := [(1,[(a,1) ; (b,2)]) ; (2, [(a,2) ; (b,1)])].
Definition delta_ex' : Alphabet -> nat -> option nat :=
graphe_vers_fonction delta_ex_graphe.

Definition auto_ex' := automate [a;b] [1;2] 1 [2] (delta_ex').

Example a31 : reconnait auto_ex' [] = false.
reflexivity. Qed.
Example a32 : reconnait auto_ex' [a;a;b;a;b;b] = true.
reflexivity. Qed.



(* Rappel : dans "auto_ex'" et "auto_ex" on ne s'intéresse qu'au états etats,
            PAS à TOUS les entiers, donc on met une garde sur "q". *)

Lemma delta_ex_trouve : forall q c, (appartient q [1;2] = true) ->  delta_ex' c q = delta_ex c q.
Proof.
intros q c H.
assert (q = 1 \/ q = 2) as Hq.
{ cbn in  H.
  rewrite Bool.orb_true_iff in H.
  destruct H.
  apply PeanoNat.Nat.eqb_eq in H; auto.
  rewrite Bool.orb_true_iff in H.
  destruct H.
  apply PeanoNat.Nat.eqb_eq in H; auto.
  discriminate.
}
destruct c; destruct Hq as [Hq | Hq]; rewrite Hq; trivial.
Qed.



(******************************************************************************)
(* Partie G : aller plus loin : le polymorphisme  *)
(******************************************************************************)

(* Quand on lit et a fortiori quand on écrit la fonction "appartient" on remarque
   son caractère générique sur les listes. *)

Print appartient.

(* Elle est écrite pour le type "list nat" mais si on remplace "Nat.eqb"
   par une fonction "comp_A : A -> A -> bool", "appartient" fonctionnerait
   pour un type donné "A". *)


(* EXERCICE *)
(* Définir la fonction "appartient_poly" qui prend en paramètres
    - un type A
    - une fonction de décision de l'égalité sur A 
    - un élement de x:A
    - une liste d'éléments de A 
   et renvoie true si et seulement si x est dans la liste *)
Fixpoint appartient_poly A (comp_A : A -> A -> bool) (x : A) (l : list A) : bool :=
  match l with
  | nil   => false
  | h::rl => (comp_A x h) || (appartient_poly A comp_A x rl)
  end.

(* Tests unitaires avec reflexivity *)
Example appartient_poly_ex1 : appartient_poly nat (Nat.eqb) 0 [1;3;0;5] = true.
Proof.
simpl. reflexivity.
Qed.
Example appartient_poly_ex2 : appartient_poly nat (Nat.eqb) 4 [1;3;0;5] = false.
Proof.
simpl. reflexivity.
Qed.

(* On peut bien sûr montrer par calcul que "appartient" est juste l'instance
   particulière de "appartient_poly nat (Nat.eqb) nat (Nat.eqb)" *)

Lemma appartient_poly_instance : forall x ls,  appartient_poly nat (Nat.eqb) x ls = appartient x ls.
Proof.
intros x ls.
induction ls.
- simpl. reflexivity.
- simpl. rewrite IHls. reflexivity.
Qed.

(* Pour bien représenter *l'appartenance* à la liste, il faut quand même s'assurer
   que "comp_A" respecte la spécification 'décider de l'égalité dans "A"'.
   Les exemples suivants montrent des choix arbitraires de "comp_A". *)

Example appartient_poly_ex3 : appartient_poly nat (fun x y => false) 0 [1;3;0;5] = false.
Proof.
simpl. reflexivity.
Qed.

Example appartient_poly_ex4 : appartient_poly nat (fun x y => true) 4 [1;3;0;5] = true.
Proof.
simpl. reflexivity.
Qed.


(* Si on veut prouver le lemme équivalent pour "appartient_poly", on a besoin
   d'une propriété de type "forall x y:A, comp_A x y = true <-> x = y"
   similaire à "PeanoNat.Nat.eqb_eq", "comp_alphabet_eq", "comp_option_nat_correct", etc. *)

(* EXERCICE *)
(* Montrer que "appartient_poly_singleton" *)
Lemma appartient_poly_singleton : forall A (x y:A) (comp : A -> A -> bool), 
      (comp x y = true <-> x = y) -> appartient_poly A comp x [y] = true <-> x = y.
Proof.
intros A x y comp Hcomp.
simpl; rewrite Bool.orb_false_r; rewrite Hcomp; split; trivial.
Qed.

(* On peut même aller plus loin et montrer que "(comp x y = true <-> x = y)" est 
  non seulement SUFFISANTE mais aussi NECESSAIRE si on veut "appartient_poly A comp x [y] = true <-> x = y" *)

(* EXERCICE *)
(* Montrer que "appartient_poly_comp" *)
Lemma appartient_poly_comp : forall A (x y:A) (comp : A -> A -> bool), 
      (appartient_poly A comp x [y] = true <-> x = y) -> (comp x y = true <-> x = y).
Proof.
intros A x y comp Hsingl.
rewrite <- Hsingl.
simpl; rewrite Bool.orb_false_r; split; trivial.
Qed.


(* Il en est de même pour "trouve" et "trouve2" *)

Print trouve.
Print trouve2.

(* EXERCICE *)
(* Définir la fonction "trouve_poly", version polymorphe de "trouve" et "trouve2" *)
Fixpoint trouve_poly KT VT (comp_K : KT -> KT -> bool) (assoc : list (KT * VT)) (key : KT) : option VT :=
  match assoc with
    | nil       => None
    | h::rassoc => if (comp_K key (fst h)) then (Some (snd h))
                   else trouve_poly KT VT comp_K rassoc key
  end.

(* EXERCICE *)
(* Montrer que "trouve" et "trouve2" sont bien des instances de "trouve_poly" *)
Lemma trouve_poly_instance_1 : forall ls k, trouve_poly Alphabet nat (comp_alphabet) ls k = trouve ls k.
Proof.
intros ls k.
induction ls ; auto.
simpl.
rewrite IHls.
reflexivity.
Qed.

Lemma trouve_poly_instance_2 : forall ls k, trouve_poly nat (list (Alphabet * nat)) (Nat.eqb) ls k = trouve2 ls k.
Proof.
intros ls k.
induction ls ; auto.
simpl.
rewrite IHls.
reflexivity.
Qed.

