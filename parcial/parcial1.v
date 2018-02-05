(* Alumno: Agustín Mista *)
(* Fecha:        2/11/17 *)

(* ------------------------------ *)
(*          Ejercicio 1           *)
(* ------------------------------ *)
Section Ejercicio1.

  Variable LEAL : Prop.        (* El general es leal *)
  Variable OBEDECE : Prop.     (* El general obedece las órdenes *)
  Variable INTELIGENTE : Prop. (* El general es inteligente *)
  Variable COMPRENDE : Prop.   (* El general comprende las órdenes *)


  (* Si el general era leal, habría obedecido las órdenes. *)
  Hypothesis H1 : LEAL -> OBEDECE. 

  (* Si el general era inteligente, las habría comprendido (las órdenes). *)
  Hypothesis H2 : INTELIGENTE -> COMPRENDE. 

  (* O el general desobedeció las órdenes o no las comprendió. *)
  Hypothesis H3 : ~OBEDECE \/ ~COMPRENDE.

  (* Luego, el general era desleal o no era inteligente. *)
  Lemma lemma1 : ~LEAL \/ ~INTELIGENTE.
  Proof.
    unfold not in *.
    elim H3; [left | right]; intros; apply H; [apply H1 | apply H2]; assumption.
  Qed.
  
End Ejercicio1.

(* ------------------------------ *)
(*          Ejercicio 2           *)
(* ------------------------------ *)
Section Ejercicio2.

  Require Import Classical.

  Variable C : Set.
  Variable P : C -> C -> Prop.

  Lemma lemma2 : (exists x y : C, P x y) \/ ~(exists x : C, P x x).
  Proof.
    unfold not in *.
    elim classic with (P := exists x y : C, P x y).
    - left. assumption.
    - right. intros. elim H. elim H0. intros. exists x. exists x. assumption.
  Qed.

End Ejercicio2.

(* ------------------------------ *)
(*          Ejercicio 3           *)
(* ------------------------------ *)
Section Ejercicio3.

  Variable U : Set.
  Variable a : U.
  Variables P Q R T : U -> Prop.

  (* 3.1 *)
  Lemma Ej3_1 : (forall x : U, P x -> Q x) -> P a -> Q a.
  Proof.
    intros. exact (H a H0).
  Qed.

  (* 3.2 *)
  Lemma Ej3_2 : (forall x : U, P x -> Q x) -> (forall x : U, Q x -> R x)
                -> (forall x : U, P x -> R x).
  Proof.
    intros. exact (H0 x (H x H1)).
  Qed.

  (* 3.3 *)
  Lemma Ej3_3 : (forall x : U, Q x) \/ (forall y : U, T y)
                -> forall z : U, Q z \/ T z.
  Proof.
    intros. elim H; intros; [left | right]; exact (H0 z).
  Qed.
 
End Ejercicio3.

(* ------------------------------ *)
(*          Ejercicio 4           *)
(* ------------------------------ *)
Section Ejercicio4.

  Parameter ABnat : forall n : nat, Set.

  (* 4.1 *)
  Parameter null : ABnat O.

  (* 4.2 *)
  Parameter add : forall n m: nat, ABnat n -> nat -> ABnat m -> ABnat (n+m+1).

  (* 4.3 *)
  Definition leftTree : ABnat 1 := add 0 0 null 7 null.  
  Definition rightTree : ABnat 1 := add 0 0 null 9 null.  
  Definition myTree : ABnat 3 := add 1 1 leftTree 8 rightTree.  
 
End Ejercicio4.