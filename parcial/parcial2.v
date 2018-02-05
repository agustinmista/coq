(* NOMBRE COMPLETO: Agustín Mista *)

Section Problema1.

  Require Export List.
  Require Export Arith.
  Print beq_nat.

  Set Implicit Arguments.

  (* 1.a *)
  Fixpoint eliminar (z : nat) (l : list nat) : list nat :=
    match l with
    | nil => nil
    | cons x xs =>
      if beq_nat x z
      then xs
      else cons x (eliminar z xs)
    end.

  (* 1.b *)
  Fixpoint pertenece (z : nat) (l : list nat) : bool :=
    match l with
    | nil => false
    | cons x xs =>
      if beq_nat x z
      then true
      else pertenece z xs
    end.

  (* 1.c *)
  Fixpoint concatenar (A : Set) (l1 l2 : list A) : list A :=
    match l1 with
    | nil => l2
    | cons x l1' => cons x (concatenar l1' l2)
    end.

  (* 1.d.1 *)
  Lemma L1_1 : forall (A : Set) (l : list A) (x : A), l <> x::l.
  Proof. 
    intros. induction l; unfold not; intros.
    - discriminate.
    - injection H. intros.
      apply IHl. rewrite <- H1. auto.
  Qed.

  (* 1.d.2 *)
  Lemma L1_2 : forall (l1 l2 : list nat) (x : nat), 
      pertenece x (concatenar l1 l2) = true -> 
      pertenece x l1 = true \/ pertenece x l2 = true.
  Proof.
    intros. induction l1.
    - simpl in H. right. auto.
    - simpl in H. case (a =? x) eqn:eq1.
      + simpl. rewrite eq1. left. auto.
      + apply IHl1 in H. elim H; intros.
        * left. simpl. rewrite eq1. auto.
        * right. auto.
  Qed.
  
  (* 1.d.3 *)
  Lemma L1_3 : forall (l : list nat) (x : nat), 
      pertenece x l = true -> eliminar x l <> l.
  Proof. 
    intros. induction l.
    - inversion H.
    - simpl. case (a =? x) eqn:eq1.
      + apply L1_1.
      + simpl in H. rewrite eq1 in H.
        apply IHl in H. injection.
        contradiction.
  Qed.

End Problema1.


Section Problema2.

  Require Import Coq.Bool.Bool.

  (* 2.a *)
  Inductive distintas (A:Set) : list A -> list A -> Prop :=
  | distintas_nil : distintas nil nil
  | distintas_cons : forall l1 l2 x y,
      x <> y -> distintas l1 l2 -> distintas (cons x l1) (cons y l2).

  Hint Constructors distintas.

  (* 2.b *)
  Lemma L2 : forall (l1 : list bool), { l2 : list bool | distintas l1 l2 }.
  Proof. 
    intros. induction l1.
    - exists nil. auto.
    - elim IHl1. intros. exists (cons (negb a) x). constructor; auto.
      case a eqn:eq1; simpl; unfold not; intros; discriminate.
  Qed.

End Problema2.

(* 2.3 *)
Extraction Language Haskell.
Extract Inductive bool => "Bool" [ "true" "false" ].
Extraction "L2" L2.

Section Problema3.
 
  Definition Var := nat.
  Definition Valor := nat.

  Definition Memoria := Var -> Valor.

  (* 3.a *)
  Inductive Instr : Set :=
  | IVar : Var -> Valor -> Instr
  | ISeq : Instr -> Instr -> Instr
  | IIf  : Var -> Valor -> Instr -> Instr -> Instr.

  (* 3.b *)
  Definition lookup (m : Memoria) (v : Var) : Valor := m v.

  Definition update (m : Memoria) (v : Var) (w : Valor) : Memoria := 
    fun v' => if beq_nat v v'
              then w
              else m v'.
  
  (* 3.c *)
  Inductive Execute : Memoria -> Instr -> Memoria -> Prop :=
  | XAss : forall var val mem,
      Execute mem (IVar var val) (update mem var val)
  | XSeq : forall ins1 ins2 mem1 mem2 mem3,
      Execute mem1 ins1 mem2
      -> Execute mem2 ins2 mem3
      -> Execute mem1 (ISeq ins1 ins2) mem3
  | XIfT : forall var val ins1 ins2 mem1 mem2,
      lookup mem1 var = val
      -> Execute mem1 ins1 mem2
      -> Execute mem1 (IIf var val ins1 ins2) mem2 
  | XIfF : forall var val ins1 ins2 mem1 mem2,
      lookup mem1 var <> val
      -> Execute mem1 ins2 mem2
      -> Execute mem1 (IIf var val ins1 ins2) mem2. 

  Hint Constructors Execute.

  (* 3.d *)
  Lemma L3_1 : forall (m1 m2 : Memoria) (var : Var) (val : Valor), 
      Execute m1 (IVar var val) m2 -> lookup m2 var = val.
  Proof.
    intros. inversion H. unfold update, lookup.
    rewrite <- beq_nat_refl. auto.
  Qed.

  Lemma L3_2 : forall (m1 m2 : Memoria) (v : Var) (val : Valor) (i1 i2 : Instr), 
      lookup m1 v <> val
      -> Execute m1 (IIf v val i1 i2) m2
      -> Execute m1 i2 m2.
  Proof.
    intros. unfold not in H.
    inversion_clear H0; auto.
    contradiction.
  Qed.

  Require Import Omega.

  Lemma L3_3: forall (m1 m2 m3 : Memoria) (v1 v2 : Var) (val : Valor) (i1 i2 : Instr),
      v2 <> v1
      -> Execute m1 (ISeq (IVar v1 val) (IVar v2 (val + 1))) m2
      -> Execute m2 i2 m3
      -> Execute m2 (IIf v2 (lookup m2 v1) i1 i2) m3.
  Proof.
    intros. apply XIfF.
    - inversion H0. inversion H5. rewrite <- H9 in H7. inversion H7.
      unfold lookup, update. rewrite <- beq_nat_refl. rewrite <- beq_nat_refl.
      elim (beq_nat_false_iff v2 v1). intros. rewrite (H17 H). omega.
    - inversion H0. auto.
  Qed.
 
End Problema3.
