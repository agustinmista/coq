(* Alumno: Agustín Mista *)
(* Fecha:       23/11/17 *)

Extraction Language Haskell.

(* ------------------------------ *)
(*          Ejercicio 3           *)
(* ------------------------------ *)

(* 3.1 *)
Definition Value := bool.

Inductive BoolExpr :=
| bbool : bool -> BoolExpr
| band : BoolExpr -> BoolExpr -> BoolExpr
| bnot : BoolExpr -> BoolExpr.

Inductive BEval : BoolExpr -> Value -> Prop :=
| ebool : forall b, BEval (bbool b) (b:Value)
| eandl : forall e1 e2, BEval e1 false -> BEval (band e1 e2) false
| eandr : forall e1 e2, BEval e2 false -> BEval (band e1 e2) false
| eandrl : forall e1 e2, BEval e1 true -> BEval e2 true -> BEval (band e1 e2) true
| enott : forall e, BEval e true -> BEval (bnot e) false
| enotf : forall e, BEval e false -> BEval (bnot e) true.

Hint Constructors BoolExpr BEval.

Fixpoint beval1 e :=
  match e with
  | bbool b => b
  | band e1 e2 =>
    match beval1 e1, beval1 e2 with
    | true, true => true
    | _, _ => false
    end
  | bnot e1 => if beval1 e1 then false else true
  end.

Fixpoint beval2 e :=
  match e with
  | bbool b => b
  | band e1 e2 =>
    match beval2 e1 with
    | false => false
    | _ => beval2 e2
    end
  | bnot e1 => if beval2 e1 then false else true
  end.

(* 3.2 *)
Lemma beval1C : forall e, {b | BEval e b}.
Proof.
  intros. exists (beval1 e). induction e; simpl; auto.
  - destruct (beval1 e1); destruct (beval1 e2); auto.
  - destruct (beval1 e); auto.
Qed.

Lemma beval2C : forall e, {b | BEval e b}.
Proof.
  intros. exists (beval2 e). induction e; simpl; auto.
  - destruct (beval2 e1); destruct (beval2 e2); auto.
  - destruct (beval2 e); auto.
Qed.

(* 3.3 y 3.4 *)
Extract Inductive bool => "Bool" [ "true" "false" ].
Extraction "beval1" beval1C.
Extraction "beval2" beval2C.


(* ------------------------------ *)
(*          Ejercicio 5           *)
(* ------------------------------ *)

(* 5.1 *)
Inductive Le : nat -> nat -> Prop :=
| Le_zero : forall n, Le O n
| Le_succ : forall n1 n2, Le n1 n2 -> Le (S n1) (S n2).

Inductive Gt : nat -> nat -> Prop :=
| Gt_zero : forall n, Gt (S n) 0
| Gt_succ : forall n1 n2, Gt n1 n2 -> Gt (S n1) (S n2).

Hint Constructors Le Gt.

(* 5.2 *)
Function leBool n1 n2 :=
  match n1, n2 with
  | 0, _ => true
  | S _, 0 => false
  | S n1', S n2' => leBool n1' n2'
  end.


Lemma Le_Gt_dec: forall n m, {Le n m} + {Gt n m}.
Proof.
  intros.
  functional induction (leBool n m); auto.
  elim IHb; intros; [ left | right ]; auto.
Qed.

(* 5.3 *)
Require Import Omega.

Lemma le_gt_dec : forall n m, {le n m} + {gt n m}.
Proof.
  intros.
  functional induction (leBool n m);
    [ left | right | elim IHb; intros; [ left | right ] ]; omega.
Qed.


(* ------------------------------ *)
(*          Ejercicio 6           *)
(* ------------------------------ *)

Require Import Omega.
Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult.

Definition spec_res_nat_div_mod a b qr :=
  match qr with
  | (q, r) => (a = b * q + r) /\ r < b
  end.

Definition nat_div_mod : forall a b,
    ~ (b = 0) -> { qr | spec_res_nat_div_mod a b qr }.
Proof.
  intros. unfold spec_res_nat_div_mod. induction a.
  - exists (0,0). omega.
  - elim IHa. intros. destruct x as (q', r').
    elim (lt_dec r' (b - 1)); intros.
    + exists (q', S r'). split; omega.
    + exists (S q',  0). split; try omega.
      * assert (S r' = b). omega.
        rewrite <- H0. rewrite mult_succ_r. rewrite H0 at 1. omega.
Qed.

Extraction "natdivmod" nat_div_mod.


(* ------------------------------ *)
(*          Ejercicio 7           *)
(* ------------------------------ *)

Inductive tree' (A:Set) : Set :=
| leaf' : tree' A
| node' : A -> tree' A -> tree' A -> tree' A.

Inductive tree_sub A t : tree' A -> Prop :=
| tree_sub1 : forall t' x, tree_sub A t (node' A x t t')
| tree_sub2 : forall t' x, tree_sub A t (node' A x t' t).

Hint Constructors tree' tree_sub.

Theorem well_founded_tree_sub : forall A, well_founded (tree_sub A).
Proof.
  unfold well_founded. intros.
  induction a; apply Acc_intro; intros; inversion H; auto.
Qed.


(* ------------------------------ *)
(*          Ejercicio 8           *)
(* ------------------------------ *)

Require Import Wf_nat.
Require Import Inverse_Image.

Fixpoint size e :=
  match e with
  | bbool _ => 1
  | band e1 e2 => S (size e1 + size e2)
  | bnot e1 => S (size e1)
  end.

Definition elt e1 e2 := size e1 < size e2.

Theorem well_founded_elt : well_founded elt.
Proof.
  apply (wf_inverse_image BoolExpr nat lt size); apply lt_wf.
Qed.