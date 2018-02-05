(* Alumno: Agustín Mista *)
(* Fecha:        10/9/17 *)

(* ------------------------------ *)
(*          Ejercicio 3           *)
(* ------------------------------ *)

Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Definition H1 := forall x : U, (R x x).
Definition H2 := forall x y z : U, (R x y) /\ (R x z) -> (R y z).

Definition Reflexiva  := forall x : U, (R x x).
Definition Simetrica  := forall x y : U, (R x y) -> (R y x).
Definition Transitiva := forall x y z : U, (R x y) /\ (R y z) -> (R x z).

(*
  Esta táctica es útil cuando tenemos que probar cosas de la forma:
       A ∧ B → C
  ya que introduce A ∧ B y lo elimina en dos hipótesis en un solo paso.
*)
Ltac exportation :=
  let H := fresh in
  match goal with
    |- _ /\ _ -> _ => intros H; elim H; intros; clear H
  end.

(*
  Esta táctica elimina varios /\ a la vez, en goals de la forma:
       A1 ∧ A2 ∧ ... ∧ An
  generando un sub-goal para cada Ai. 
*)
Ltac split_many :=
  match goal with
    |- _ => split; repeat try split
  end.

(* Ej 3.1 *)
Theorem e231: H1 /\ H2 -> Reflexiva /\ Simetrica /\ Transitiva.  
Proof.
  unfold H1, H2, Reflexiva, Simetrica, Transitiva in *.
  exportation. split_many.
  - (* Reflexiva *)
    assumption.
  - (* Simetrica *)
    intros. apply (H3 x y x). split; [ assumption | apply H0].
  - (* Transitiva *)
    intros x y z. exportation. apply (H3 y x z). split; [ | assumption ].
     + apply (H3 x y x). split; [ assumption | apply H0 ].
Qed.

Definition Irreflexiva := forall x : U, ~ (R x x). 
Definition Asimetrica := forall x y : U, (R x y) -> ~ (R y x).
 
(* Ej 3.2 *)
Lemma e232 : Asimetrica -> Irreflexiva.
Proof.
  unfold Asimetrica, Irreflexiva, not.
  intros. apply (H x x); assumption.
Qed.

End Ejercicio3.

(* ------------------------------ *)
(*          Ejercicio 7           *)
(* ------------------------------ *)

Section Ejercicio7.

Variable U : Set.
Variable A B : U -> Prop.

(* Ej 7.1 *)
Theorem e71: (forall x : U, ((A x) /\ (B x))) -> (forall x : U, (A x)) /\ (forall x : U, (B x)).
Proof.
  intros. split; intros; apply H.
Qed.

(* Ej 7.2 *)
Theorem e72: (exists x : U, (A x \/ B x)) -> (exists x : U, A x) \/ (exists x : U, B x).
Proof.
  intros. elim H. intros. elim H0; intros; [ left | right ]; exists x; assumption.
Qed.

(* Ej 7.3 *)
Theorem e73: (forall x : U, A x) \/ (forall y : U, B y) -> forall z : U, A z \/ B z.
Proof.
  intros. elim H; intros; [ left | right ]; apply H0.
Qed.

End Ejercicio7.

(* ------------------------------ *)
(*          Ejercicio 9           *)
(* ------------------------------ *)

Section Ejercicio9.
  
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

(* Ej 9.1 *)
Lemma not_ex_not_forall: (~exists x : U, ~A x) -> (forall x : U, A x).
Proof.
  unfold not. intros. elim classic with (P:= A x); intros; [ assumption | ].
  - unfold not in H0. elim H. exists x. assumption.
Qed.

(* Ej 9.2 *)
Lemma not_forall_ex_not: (~forall x : U, A x) -> (exists x : U, ~A x).
Proof.
  intros. elim classic with (P := exists x, ~ A x); intros; [ assumption | ].
  - elim H. apply not_ex_not_forall. assumption.
Qed.
  
End Ejercicio9.

(* ------------------------------ *)
(*          Ejercicio 10          *)
(* ------------------------------ *)

Section Ejercicio10.

Variable nat : Set.
Variable O : nat.
Variable S : nat -> nat.

Axiom disc : forall n : nat, ~ (O = (S n)).
Axiom inj : forall n m : nat, (S n) = (S m) -> n = m.
Axiom allNat : forall n : nat, (n = O) \/ (exists m : nat, S m = n).

Variable sum prod : nat -> nat -> nat.

Axiom sum0 : forall n : nat, (sum n O) = n.
Axiom sumS : forall n m : nat, (sum n (S m)) = (S (sum n m)).
Axiom prod0 : forall n : nat, (prod n O) = O.
Axiom prodS : forall n m : nat, (prod n (S m)) = (sum n (prod n m)).

(* Ej 10.1 *)
Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
  intros. rewrite sumS. rewrite sum0. reflexivity.
Qed.

(* Ej 10.2 *)
Lemma L10_2: forall n :nat, ~ ((O=n) /\ (exists m : nat, n = (S m))).
Proof.
  unfold not. intros. elim H; intros.
  rewrite <- H0 in H3. elim H3. apply disc.  
Qed.

(* Ej 10.3 *)
Lemma prod_neutro: forall n : nat, (prod n (S O)) = n.
Proof.
  intros. rewrite prodS. rewrite prod0. rewrite sum0. reflexivity.
Qed.

(* Ej 10.4 *)
Lemma diff: forall n : nat, ~ (S (S n)) = (S O).
Proof.
  intros. unfold not. intros. apply inj in H. symmetry in H.
  apply disc in H. contradiction.  
Qed.

(* Ej 10.5 *)
Lemma L10_3: forall n: nat, exists m : nat, prod n (S m) = sum n n. 
Proof.
  intros. exists (S O).
  rewrite prodS. rewrite prodS. rewrite prod0. rewrite sum0. reflexivity.
Qed.

(* Ej 10.6 *)
Lemma L10_4: forall m n : nat, n <> O -> sum m n <> O.  
Proof.
  unfold not. intros. elim (allNat n); [ assumption | ].
  - intros. elim H3. intros.
    rewrite <- H4 in H0. rewrite sumS in H0.
    apply (disc (sum m x)). symmetry. assumption.
Qed.

(* Ej 10.7 *)
Lemma L10_5: forall m n : nat, sum m n = O -> m = O /\ n = O.  
Proof.
  intros. elim (allNat n); intros.
  - rewrite H0 in H. rewrite sum0 in H. split; assumption.
  - elim H0. intros. rewrite <- H3 in H. rewrite sumS in H.
    elim (disc (sum m x)). symmetry. assumption.
Qed.
              
End Ejercicio10.