(* Alumno: Agustín Mista *)
(* Fecha:         2/9/17 *)

Section P1.
Variables A B C:Prop.

(* ------------------------------ *)
(*          Ejercicio 5           *)
(* ------------------------------ *)

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
  intros. unfold not. intros. apply H in H1. contradiction.
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
  unfold not. intros. elim H. intros. apply H1. assumption.
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
  intros. unfold not. intros. elim H0. intros.
  apply H2. apply H. assumption.
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
  intros. unfold not. intros. apply H0.
  - elim H. intros. assumption.
  - elim H. intros. assumption.  
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
  intros. elim H. unfold not. intros. apply H1. assumption.
Qed.

(* ------------------------------ *)
(*          Ejercicio 6           *)
(* ------------------------------ *)

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
  intros. unfold not. intros. elim H0.
  intros. elim H.
  - assumption.
  - assumption.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
  unfold iff. split.
  - intros. elim H.
    + right. assumption.
    + left. assumption.
  - intros. elim H.
    + right. assumption.
    + left. assumption. 
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
  intros. elim H.
  + assumption.
  + intros. assumption.
Qed.

End P1.

Section Logica_Clasica.
Variables A B C: Prop.

Require Import Classical.
Check classic.

(* ------------------------------ *)
(*          Ejercicio 8           *)
(* ------------------------------ *)

(* Ej 8.1 *)
Theorem e81: forall A:Prop, ~~A->A .
Proof.
  intros. elim classic with (P:=A0).
  - intros. assumption.
  - intros. contradiction.
Qed. 

(* Ej 8.2 *)
Theorem e82: forall A B:Prop, (A->B)\/(B ->A).
Proof.
  intros. elim classic with (P:=A0).
  - intros. right. intros. assumption.
  - intros. left. intros. contradiction. 
Qed.

(* Ej 8.3 *)
Theorem e83: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
  intros. unfold not in H. 
  elim classic with (P:= A0).
  - intros. right. unfold not. intros. apply H. split.
    + assumption.
    + assumption.
  - intros. left. assumption.
Qed.
   
End Logica_Clasica.

Section Traducciones.

(* ------------------------------ *)
(*          Ejercicio 9           *)
(* ------------------------------ *)

(* Definiciones *)
Variable NM RED CONS UTIL : Prop.

Hypothesis H1 : ~NM \/ ~RED.
Hypothesis H2 : CONS \/ ~UTIL.

Theorem ej9 : (NM /\ UTIL) -> (CONS /\ ~RED).
Proof.
  intros. split.
  + elim H2.
    - intros. assumption.
    - intros. elim H. intros. contradiction.
  + elim H1. 
    - intros. elim H. intros. contradiction.
    - intros. assumption.
Qed.

End Traducciones.

Section Ej12.

(* ------------------------------ *)
(*          Ejercicio 12          *)
(* ------------------------------ *)

(* Definiciones *)

Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

Hypothesis Regla1: PF \/ PA -> PH \/ PR.
Hypothesis Regla2: ~PR \/ PF.
Hypothesis Regla3: PH /\ ~PR -> PA.

Theorem ej12: (~PA /\ PF) -> PR.
Proof.
  intros. elim H. intros. elim Regla1.
  + intros. elim classic with (P:=PR). 
    - intros. assumption.
    - intros. assert (PH /\ ~PR). 
        * split. assumption. assumption. 
        * assert PA. apply Regla3. assumption. contradiction. 
  + intros. assumption.
  + left. assumption.
Qed.

End Ej12.