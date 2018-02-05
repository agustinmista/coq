(* Alumno: Agustín Mista *)
(* Fecha:       29/10/17 *)


(* ------------------------------ *)
(*          Ejercicio 1           *)
(* ------------------------------ *)
Section Ejercicio1.

  (* 1.1 *)
  Inductive list (A : Set) : Set :=
    nil : list A
  | cons : A -> list A -> list A. 

  Inductive bintree (A : Set) : Set :=
    leaf : bintree A
  | node : bintree A -> A -> bintree A -> bintree A.

  (* 1.2 *)
  Inductive array (A : Set) : nat -> Set :=
    emptyA : array A 0
  | addA : forall n : nat, A -> array A n -> array A (n+1).

  Inductive matrix (A : Set) : nat -> nat -> Set :=
    emptyM : matrix A 0 0
  | addRow : forall m n : nat, array A m -> matrix A (m+1) n 
  | addCol : forall m n : nat, array A n -> matrix A m (n+1). 

  (* 1.3 *)
  Inductive leq : nat -> nat -> Prop :=
    leq_O : forall n : nat, leq O n
  | leq_S : forall m n : nat, leq m n -> leq (S m) (S n).

  (* 1.4 *)
  Inductive eq_list (A : Set) : list A -> list A -> Prop :=
    eq_nil : eq_list A (nil A) (nil A)
  | eq_cons : forall (e : A) (xs ys : list A)
    , eq_list A xs ys -> eq_list A (cons A e xs) (cons A e ys). 

  (* 1.5 *)
  Inductive sorted (A : Set) (R : A -> A -> Prop) : list A -> Prop :=
    sorted_nil : sorted A R (nil A)
  | sorted_sin : forall (x : A), sorted A R (cons A x (nil A))
  | sorted_rec : forall (x1 x2 : A) (xs : list A)
    , R x1 x2 -> sorted A R xs -> sorted A R (cons A x1 (cons A x2 xs)). 

  (* 1.6 *)
  Inductive mirror (A : Set) : bintree A -> bintree A -> Prop :=
    mirror_leaf : mirror A (leaf A) (leaf A)
  | mirror_node : forall (x : A) (a b c d : bintree A)
    , mirror A a d -> mirror A b c -> mirror A (node A a x b) (node A c x d).

  (* 1.7 *)
  Inductive isomorfo (A : Set) : bintree A -> bintree A -> Prop :=
    iso_leaf : isomorfo A (leaf A) (leaf A)
  | iso_node : forall (e1 e2 : A) (l1 l2 r1 r2 : bintree A)
    , isomorfo A l1 l2 -> isomorfo A r1 r2
      -> isomorfo A (node A l1 e1 r1) (node A l2 e2 r2).

End Ejercicio1.

(* ------------------------------ *)
(*          Ejercicio 3           *)
(* ------------------------------ *)
Section Ejercicio3.

  (* 3.1 *)
  Fixpoint sum (x y : nat) : nat :=
    match y with
    | O => x
    | S y => S (sum x y)
    end.

  (* 3.2 *)
  Fixpoint plus (x y : nat) : nat :=
    match y with
    | O => O
    | S y => sum x (plus x y)
    end.

  (* 3.3 *)
  Fixpoint pot (x y : nat) : nat :=
    match y with
    | O => S O
    | S y => plus x (pot x y)
    end.

  (* 3.4 *)
  Fixpoint leBool (x y : nat) : bool :=
    match x, y with
    | O, _ => true
    | S x, O => false
    | S x, S y => leBool x y
    end.

End Ejercicio3.


(* ------------------------------ *)
(*          Ejercicio 4           *)
(* ------------------------------ *)
Section Ejercicio4.

  (* 4.1 *)
  Fixpoint length (A : Set) (xs : list A) : nat :=
    match xs with
    | nil _ => O
    | cons _ _ xs => 1 + (length A xs)
    end.

  (* 4.2 *)
  Fixpoint append (A : Set) (xs ys : list A) : list A :=
    match xs with
    | nil _ => ys
    | cons _ x xs => cons A x (append A xs ys)
    end.

  (* 4.3 *)
  Fixpoint reverse (A : Set) (xs : list A) : list A :=
    match xs with
    | nil _ => nil A
    | cons _ x xs => append A (reverse A xs) (cons A x (nil A))
    end.

  (* 4.4 *)
  Fixpoint filter (A : Set) (p : A -> bool) (xs : list A) : list A :=
    match xs with
    | nil _ => nil A
    | cons _ x xs =>
      if (p x)
      then cons A x (filter A p xs)
      else filter A p xs
    end.

  (* 4.5 *)
  Fixpoint map (A B : Set) (f : A -> B) (xs : list A) : list B :=
    match xs with
    | nil _ => nil B
    | cons _ x xs => cons B (f x) (map A B f xs)
    end.

  (* 4.6 *)
  Fixpoint exists_ (A : Set) (p : A -> bool) (xs : list A) : bool :=
    match xs with
    | nil _ => false
    | cons _ x xs =>
      if p x
      then true
      else exists_ A p xs
    end.

End Ejercicio4.


(* ------------------------------ *)
(*          Ejercicio 9           *)
(* ------------------------------ *)
Section Ejercicio5.

  Fixpoint inverse (A : Set) (t : bintree A) : bintree A :=
    match t with
    | leaf _ => leaf A
    | node _ l x r => node A (inverse A r) x (inverse A l)
    end.

End Ejercicio5.


(* ------------------------------ *)
(*          Ejercicio 9           *)
(* ------------------------------ *)
Section Ejercicio9.

  (* 9.1 *)
  Lemma SumO : forall n : nat, sum n O = n /\ sum O n = n.
  Proof.
    intros. induction n.
    (* n = 0 *)
    - split; reflexivity.
    (* n = S n' *)
    - elim IHn. intros IH1 IH2. split; simpl; [idtac | rewrite IH2]; reflexivity.
  Qed.

  (* 9.2 *)
  Lemma SumS : forall n m : nat, sum n (S m) = sum (S n) m.
  Proof.
    intros. induction m.
    (* m = 0 *)
    - reflexivity.
    (* m = S m' *)
    - simpl. rewrite <- IHm. reflexivity.
  Qed.

  (* 9.3 *)
  Lemma SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
  Proof.
    intros. induction p.
    (* p = 0 *)
    - reflexivity.
    (* p = S p' *)
    - simpl. rewrite <- IHp. reflexivity.
  Qed.

  (* 9.4 *)
  Lemma SumConm : forall n m : nat, sum n m = sum m n.
  Proof.
    intros. induction m.
    (* m = 0 *)
    - elim SumO with (n := n). intros H1 H2. rewrite H1. rewrite H2. reflexivity.
    (* m = S m' *)
    - elim SumS. simpl. rewrite IHm. reflexivity.
  Qed.

End Ejercicio9.


(* ------------------------------ *)
(*          Ejercicio 12          *)
(* ------------------------------ *)
Section Ejercicio12.

  (* 12.1 *)
  Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B),
    map A B f (append A l m) = append B (map A B f l) (map A B f m).
  Proof.
    intros. induction l.
    (* l = nil *)
    - reflexivity.
    (* l = cons x l' *)
    - simpl. rewrite IHl. reflexivity.
  Qed.

  (* 12.2 *)
  Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
    filter A P (append A l m) = append A (filter A P l) (filter A P m).
  Proof.
    intros. induction l.
    (* l = nil *)
    - reflexivity.
    (* l = cons x l' *)
    - simpl. case (P a); rewrite IHl; reflexivity.
  Qed.

  (* 12.3 *)
  Lemma L9 : forall (A : Set) (l : list A) (P : A -> bool),
    filter A P (filter A P l) = filter A P l. 
  Proof.
    intros. induction l.
    (* l = nil *)
    - reflexivity.
    (* l = cons x xs *)
    - simpl. case (P a) eqn:eq1.
      + simpl. case (P a) eqn:eq2.
        * rewrite IHl. reflexivity.
        * discriminate.
      + assumption.
  Qed.

  (* 12.4 *)
  Lemma L10 : forall (A : Set) (l m n : list A),
    append A l (append A m n) = append A (append A l m) n. 
  Proof.
    intros. induction l.
    (* l = nil *)
    - reflexivity.
    (* l = cons x *)
    - simpl. rewrite IHl. reflexivity.
  Qed.

End Ejercicio12.


(* ------------------------------ *)
(*          Ejercicio 14          *)
(* ------------------------------ *)
Section Ejercicio14.

  Theorem inverse_mirror : forall (A : Set) (t : bintree A),
    mirror A (inverse A t) t.
  Proof.
    intros. induction t.
    (* t = leaf *)
    - constructor.
    (* t = node l x r *)
    - constructor; assumption.
  Qed.

End Ejercicio14.


(* ------------------------------ *)
(*          Ejercicio 17          *)
(* ------------------------------ *)
Section Ejercicio17.

  (* 17.1 *)
  Inductive postfix (A : Set) : list A -> list A -> Prop :=
  | postfix_refl : forall (l : list A), postfix A l l
  | postfix_cons : forall (x : A) (l1 l2 : list A)
    , postfix A l1 l2 -> postfix A l1 (cons A x l2).

  Notation "l1 << l2" := (postfix _ l1 l2) (at level 50).
  Notation "l1 +++ l2" := (append _ l1 l2) (at level 40).

  (* 17.2.1 *)
  Theorem list_postfix_append : forall (A : Set) (l1 l2 l3 : list A),
      l2 = l3 +++ l1 -> l1 << l2.
  Proof.
    intros. rewrite H. clear H. induction l3.
    (* l3 = nil *)
    - simpl. constructor.
    (* l3 = cons x xs *)
    - simpl. apply postfix_cons. apply IHl3. 
  Qed.

  (* 17.2.2 *)
  Theorem list_postfix_exists : forall (A : Set) (l1 l2 :list A),
      l1 << l2 -> (exists l3 : list A, l2 = l3 +++ l1).
  Proof.
    intros. induction H.
    - exists (nil A).
      simpl. reflexivity.
    - elim IHpostfix. intros.
      exists (cons A x x0).
      simpl. rewrite H0. reflexivity.
  Qed.

  (* 17.3.1 *)
  Lemma list_postfix_neutral : forall (A : Set) (l1 l2 : list A), l2 << l1 +++ l2.
  Proof.
    intros. induction l1.
    (* l1 = nil *)
    - simpl. constructor.
    (* l1 = cons x xs *)
    - simpl. constructor. assumption. 
  Qed.

  (* 17.3.2 *)
  Axiom list_append_nil : forall (A : Set) (l1 l2 : list A)
    , l1 = l2 +++ l1 -> l2 = nil A.

  Lemma list_append_nil2 : forall (A : Set) (l1 l2 : list A)
    , l1 +++ l2 = nil A -> l1 = nil A /\ l2 = nil A.
  Proof.
    intros. destruct l1.
    - split. reflexivity. simpl in H. assumption.
    - split; simpl in H; discriminate.
  Qed.

  Lemma list_postfix_antisymm : forall (A : Set) (l1 l2 : list A),
      l1 << l2 -> l2 << l1 -> l1 = l2.
  Proof.
    intros.
    elim (list_postfix_exists _ _ _ H); intros.
    elim (list_postfix_exists _ _ _ H0); intros.
    rewrite H1 in H2. rewrite L10 in H2.
    assert (x0 +++ x = nil _). apply (list_append_nil A l1 (x0 +++ x)). assumption.
    assert (x0 = nil _). apply (list_append_nil2 A x0 x H3).
    assert (x = nil _). apply (list_append_nil2 A x0 x H3).
    rewrite H5 in H1. simpl in H1. symmetry. assumption.
  Qed.

  (* 17.3.3 *)
  Lemma list_postfix_trans : forall (A : Set) (l1 l2 l3 : list A),
      l1 << l2 -> l2 << l3 -> l1 << l3.
  Proof.
    intros. induction H0. 
    - assumption.
    - constructor. apply IHpostfix. assumption.
  Qed.
  
  (* 17.4 *)
  Fixpoint ultimo (A : Set) (xs : list A) : list A :=
    match xs with
    | nil _ => nil A
    | cons _ x xs' =>
      match xs' with
      | nil _ => cons A x (nil A)
      | cons _ x' xs'' => ultimo A xs'
      end
    end.

  Lemma nil_is_postfix : forall (A : Set) (xs : list A), nil A << xs.
  Proof.
    intros. induction xs.
    (* xs = nil *)
    - constructor.
    (* xs = cons x xs *)
    - constructor. assumption.
  Qed.

  (* 17.5 *)
  Lemma ultimo_is_postfix : forall (A : Set) (xs : list A), ultimo A xs << xs.
  Proof.
    intros. induction xs.
    - simpl. constructor.
    - destruct xs.
      (* xs = nil *)
      + simpl. constructor.
      (* xs = cons x xs *)
      + constructor. assumption.
  Qed.

End Ejercicio17.


(* ------------------------------ *)
(*          Ejercicio 20          *)
(* ------------------------------ *)
Section Ejercicio20.

  (* 20.1 *)
  Inductive ACom (A : Set) : nat -> Set :=
    leafCom : ACom A 0
  | nodeCom : forall n : nat, ACom A n -> A -> ACom A n -> ACom A (n+1).

  (* 20.2 *)
  Fixpoint h (A : Set) (n : nat) (t : ACom A n) : nat :=
    match t with
    | leafCom _ => 1
    | nodeCom _ n l x r => (h A n l) + (h A n r)
    end.

  (* 20.3 *)
  Axiom potO : forall n : nat, pot (n + 1) 0 = 1.
  Axiom potS : forall m: nat, pot 2 (m + 1) = pot 2 m + pot 2 m.

  Lemma ACom_leaves_exp : forall (A : Set) (n : nat) (t : ACom A n),
      h A n t = pot 2 n.
  Proof.
    intros. induction t.
    (* t = leafCom *)
    - simpl. reflexivity.
    (* t = nodeCom n l x r *)
    - simpl. rewrite IHt1. rewrite IHt2.
      rewrite <- potS. reflexivity.
  Qed.

End Ejercicio20.