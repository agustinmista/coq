(* Alumno: Agustín Mista *)
(* Fecha:       14/11/17 *)


(* ------------------------------ *)
(*          Ejercicio 3           *)
(* ------------------------------ *)
Section Ejercicio3.

  (* 3.1 *)
  Variable A : Set.

  Parameter equal : A -> A -> bool.

  Axiom equal1 : forall x y, equal x y = true <-> x = y.
  Axiom equal2 : forall x, equal x x <> false.

  Inductive List :=
  | nullL : List
  | consL : A -> List -> List.

  Inductive MemL (a : A) : List -> Prop :=
  | hereL : forall x, MemL a (consL a x)
  | thereL : forall x, MemL a x -> forall b, MemL a (consL b x).

  Inductive isSet : List -> Prop :=
  | emptyS : isSet nullL
  | addM : forall x xs, ~ MemL x xs -> isSet xs -> isSet (consL x xs).

  (* 3.2 *)
  Fixpoint deleteAll x xs :=
    match xs with
    | nullL => nullL
    | consL x' xs =>
      if equal x x'
      then deleteAll x xs
      else consL x' (deleteAll x xs)
    end.

  (* 3.3 *)
  Lemma DeleteAllNotMember : forall l x, ~ MemL x (deleteAll x l).
  Proof.
    induction l; intros; unfold not; intros.
    - inversion H.
    - apply IHl with (x:=x). simpl in H. case (equal x a) eqn:eq1.
      + apply IHl in H. contradiction.
      + inversion H.
        * rewrite H1 in eq1. eapply equal2 in eq1. contradiction.
        * auto.
  Qed.

  (* 3.4 *)
  Fixpoint delete x xs :=
    match xs with
    | nullL => nullL
    | consL x' xs' =>
      if equal x x'
      then xs'
      else consL x' (delete x xs')
    end.
      
  (* 3.5 *)
  Lemma DeleteNotMember : forall l x, isSet l -> ~ MemL x (delete x l).
  Proof.
    induction l; unfold not in *; intros.
    - inversion H0.
    - inversion_clear H.
      unfold not in H1. simpl in H0.
      case (equal x a) eqn:eq1.
      + elim (equal1 x a ). intros. rewrite (H eq1) in H0. auto.
      + inversion H0.
        * rewrite H3 in eq1. pose (equal2 a). contradiction.
        * apply (IHl x); auto.
  Qed.

End Ejercicio3.

(* ------------------------------ *)
(*          Ejercicio 4           *)
(* ------------------------------ *)

Section Ejercicio4.

  Variable A : Set.

  Inductive AB : Set :=
  | null : AB
  | cons : A -> AB -> AB -> AB.

  (* 4.1 *)
  Inductive Pertenece : A -> AB -> Prop :=
  | pertenece_root : forall a l r, Pertenece a (cons a l r)
  | pertenece_left : forall a b l r, Pertenece a l -> Pertenece a (cons b l r) 
  | pertenece_right : forall a b l r, Pertenece a r -> Pertenece a (cons b l r). 

  Hint Constructors Pertenece.

  Parameter eqGen : A -> A -> bool.
  Axiom eqGen1 : forall x, ~ (eqGen x x = false).

  (* 4.2 *)
  Fixpoint borrar x ab :=
    match ab with
    | null => ab
    | cons x' l r =>
      if eqGen x' x
      then null
      else cons x' (borrar x l) (borrar x r)
    end.
      
  (* 4.3 *)
  Lemma BorrarNoPertenece : forall ab a, ~ Pertenece a (borrar a ab).
  Proof.
    induction ab; unfold not in *; intros.
    - inversion H.
    - simpl in H. case (eqGen a a0) eqn:eq1.
      + inversion_clear H.
      + inversion H.
        * rewrite H2 in eq1. pose (eqGen1 a). auto.
        * apply IHab1 with (a:=a0). auto.
        * apply IHab2 with (a:=a0). auto.
  Qed.

End Ejercicio4.

(* ------------------------------ *)
(*          Ejercicio 5           *)
(* ------------------------------ *)

(* 5.1 *)
Definition Var := nat.

Inductive BoolExp :=
| BEVar  : Var -> BoolExp
| BEBool : bool -> BoolExp
| BEAnd  : BoolExp -> BoolExp -> BoolExp
| BENot  : BoolExp -> BoolExp.

Notation "'VAR' v" := (BEVar v) (at level 50).
Notation "'TRUE'" := (BEBool true) (at level 70).
Notation "'FALSE'" := (BEBool false) (at level 70).
Notation "e1 && e2" := (BEAnd e1 e2). 
Notation "¬ e" := (BENot e) (at level 60).

(* 5.2 *)
Definition Val := bool.
Definition Mem := nat -> Val.
Definition lookup (v : Var) (m : Mem) : Val := m v.

Inductive BEval : BoolExp -> Mem -> Val -> Prop :=
| EVar : forall mem var, BEval (VAR var) mem (lookup var mem)
| EBoolT : forall mem, BEval (TRUE) mem true
| EBoolF : forall mem, BEval (FALSE) mem false
| EAndLF : forall mem e1 e2,
    BEval e1 mem false -> BEval (e1 && e2) mem false
| EAndRF : forall mem e1 e2,
    BEval e2 mem false -> BEval (e1 && e2) mem false
| EAndT : forall mem e1 e2,
    BEval e1 mem true -> BEval e2 mem true -> BEval (e1 && e2) mem true
| ENotT : forall mem e, BEval e mem true -> BEval (¬ e) mem false
| ENotF : forall mem e, BEval e mem false -> BEval (¬ e) mem true.

Notation "( exp , mem )  >- val" := (BEval exp mem val) (at level 40). 

(* 5.3.1 *)
Lemma be_true_never_false : forall mem, ~ (TRUE, mem) >- false.
Proof.
  unfold not. intros. inversion H.
Qed.

(* 5.3.2 *)
Lemma be_and_neutral : forall mem e1 e2 w,
    (e1, mem) >- true -> (e2, mem) >- w -> (e1 && e2, mem) >- w.
Proof.
  intros. destruct w.
  (* w = true *)
  - constructor; auto.
  (* w = false *)
  - apply EAndRF. auto.
Qed.

(* 5.3.3 *)
Lemma beval_is_function : forall mem exp w1 w2,
    (exp, mem) >- w1 -> (exp, mem) >- w2 -> w1 = w2.
Proof.
  intros mem exp w1 w2 H1 H2.
  induction exp; inversion H1; inversion H2; auto.
  (* exp = BEBool b *)
  + rewrite <- H0 in H5. auto.
  + rewrite <- H0 in H5. auto.
  (* exp = BEAnd e1 e2 *)
  + rewrite <- H4 in *. rewrite <- H10 in *. apply IHexp1; auto.
  + rewrite <- H4 in *. rewrite <- H10 in *. apply IHexp2; auto.
  + rewrite <- H5 in *. rewrite <- H10 in *. apply IHexp1; auto.
  + rewrite <- H5 in *. rewrite <- H10 in *. apply IHexp2; auto.
  (* exp = BENot e *)
  + rewrite <- H4 in *. rewrite <- H8 in *. apply IHexp; auto.
  + rewrite <- H4 in *. rewrite <- H8 in *. apply IHexp; auto.
Qed.

(* 5.3.3 *)
(* Nota: Este ejercicio tiene un error en el enunciado *)
Lemma beval_5_3_3 : forall mem e1 e2,
    (e1, mem) >- false -> ~(e1 && e2, mem) >- true.
Proof.
  unfold not. intros mem e1 e2 H1 H2. inversion H2.
  apply (beval_is_function mem _ true false) in H3.
  discriminate. auto.

(* 5.4 *)
Fixpoint beval mem exp :=
  match exp with
  | BEVar var => lookup var mem
  | BEBool b => b
  | BEAnd e1 e2 => andb (beval mem e1) (beval mem e2) 
  | BENot e => negb (beval mem e)
  end.

(* 5.5 *)
Theorem beval_vs_BEval : forall exp mem, (exp, mem) >- (beval mem exp).
Proof.
  intros. induction exp; simpl.
  (* exp = BEVar var *)
  - constructor.
  (* exp = BEBool b *) 
  - case b; constructor.
  (* exp = BEAnd e1 e2 *)
  - destruct (beval mem exp1).
    destruct (beval mem exp2); simpl.
    + constructor; auto.
    + apply EAndRF. auto.
    + apply EAndLF. auto.
  (* exp = BENot e *)
  - destruct (beval mem exp); simpl; constructor; auto.
Qed.


(* ------------------------------ *)
(*          Ejercicio 6           *)
(* ------------------------------ *)

(* 6.1 *)
Inductive Instr :=
| ISkip : Instr
| IVar : Var -> BoolExp -> Instr
| IIf : BoolExp -> Instr -> Instr -> Instr
| IWhile : BoolExp -> Instr -> Instr
| IRepeat : nat -> Instr -> Instr
| IBlock : LInstr -> Instr
with LInstr :=
     | LIEmpty : LInstr
     | LISeq : Instr -> LInstr -> LInstr.

(* 6.2.1 *)

Notation "'SKIP'" := ISkip.
Notation "var '::=' exp" := (IVar var exp) (at level 90, right associativity).
Notation "'IF_' b 'THEN' th 'ELSE' el"
  := (IIf b th el) (at level 80, right associativity).
Notation "'WHILE' b 'DO' i "
  := (IWhile b i) (at level 80, right associativity).
Notation "'REPEAT' n # i "
  := (IRepeat n i) (at level 80, right associativity).
Notation "'BEGIN' li 'END'" := (IBlock li) (at level 90, right associativity).
Notation "'EMPTY'" := LIEmpty.
Notation "i ; li" := (LISeq i li) (at level 100, right associativity).
Notation "i ;" := (LISeq i LIEmpty) (at level 100, right associativity).


Variables X Y : Var.
Definition test : Instr :=
  IF_ TRUE && FALSE
  THEN
    BEGIN
      SKIP;
      X ::= TRUE;
      WHILE ¬FALSE DO
        SKIP;
      SKIP;
  END 
  ELSE REPEAT 3# 
    BEGIN
      Y ::= FALSE;
      SKIP;
    END.

(* 6.2.2 *)
Variables V1 V2 : Var.
Definition PP : Instr :=
  BEGIN
    V1 ::= TRUE;
    V2 ::= ¬ VAR V1;
  END.

(* 6.2.3 *)
Variable aux : Var.
Definition swap : Instr :=
  BEGIN
    aux ::= VAR V1;
    V1  ::= VAR V2;
    V2  ::= VAR aux;
  END.

(* 6.3 *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.

Definition update var val mem :=
  fun var' => if beq_nat var var' then val else lookup var' mem. 

(* 6.4 *)
Lemma lookup_update : forall mem var val, lookup var (update var val mem) = val.  
Proof.
  intros. unfold lookup, update. rewrite <- (beq_nat_refl var). auto.
Qed.

(* 6.5 *)
Lemma lookup_update' : forall mem var var' val,
    var <> var' -> lookup var' (update var val mem) = lookup var' mem.
Proof.
  intros. unfold update. unfold lookup. elim (beq_nat_false_iff var var').
  intros. apply H1 in H. rewrite H. auto.
Qed.


(* ------------------------------ *)
(*          Ejercicio 7           *)
(* ------------------------------ *)

(* 7.1 *)
Inductive Execute : Instr -> Mem -> Mem -> Prop :=
| XAss : forall mem be w var,
    (be, mem) >- w
    -> Execute (var ::= be) mem (update var w mem)
| XSkip : forall mem,
    Execute SKIP mem mem
| XIfT : forall mem mem' be th el,
    (be, mem) >- true
    -> Execute th mem mem'
    -> Execute (IF_ be THEN th ELSE el) mem mem'
| XIfF : forall mem mem' be th el,
    (be, mem) >- false
    -> Execute el mem mem'
    -> Execute (IF_ be THEN th ELSE el) mem mem'
| XWhileT : forall mem mem' mem'' be ins,
    (be, mem) >- true
    -> Execute ins mem mem'
    -> Execute (WHILE be DO ins) mem' mem''
    -> Execute (WHILE be DO ins) mem mem''
| XWhileF : forall mem be ins,
    (be, mem) >- false
    -> Execute (WHILE be DO ins) mem mem
| XRepeatO : forall mem ins,
    Execute (REPEAT 0# ins) mem mem
| XRepeatS : forall mem mem' mem'' ins n,
    Execute ins mem mem'
    -> Execute (REPEAT n# ins) mem' mem''
    -> Execute (REPEAT S n# ins) mem mem''
| XBlock : forall mem mem' seq,
    ExecuteSeq seq mem mem'
    -> Execute (IBlock seq) mem mem'
with ExecuteSeq : LInstr -> Mem -> Mem -> Prop :=
     | XEmpty : forall mem, ExecuteSeq EMPTY mem mem
     | XNext : forall mem mem' mem'' ins seq,
         Execute ins mem mem'
         -> ExecuteSeq seq mem' mem''
         -> ExecuteSeq (ins ; seq) mem mem''.

Notation "( ins , mem )  >> mem'" := (Execute ins mem mem') (at level 40).
Notation "( seq , mem )  >>> mem'" := (ExecuteSeq mem mem') (at level 40).

(* 7.2 *)
Lemma execute_if_false : forall mem mem' th el,
    (IF_ ¬ FALSE THEN th ELSE el, mem) >> mem'
    -> (IF_ FALSE THEN el ELSE th, mem) >> mem'.
Proof.
  intros. apply XIfF; inversion H; inversion H5; inversion H8; try constructor.
  auto.
Qed.

(* 7.3 *)
Lemma execute_if : forall mem mem' th el be,
    (IF_ ¬ be THEN th ELSE el, mem) >> mem'
    -> (IF_ be THEN el ELSE th, mem) >> mem'.
Proof.
  intros. inversion H; inversion H5; [ apply XIfF | apply XIfT]; auto.
Qed.

(* 7.4 *)
Lemma execute_while_false : forall mem mem' ins,
    (WHILE FALSE DO ins, mem) >> mem' -> mem = mem'.
Proof.
  intros. inversion H; inversion H2; auto.
Qed.

(* 7.5 *)
Lemma execute_while_skip : forall mem mem' ins be,
    (BEGIN IF_ be THEN ins ELSE SKIP; WHILE be DO ins; END, mem) >> mem'
    -> (WHILE be DO ins, mem) >> mem'.
Proof.
  intros. inversion H. inversion H1.
  inversion H6; inversion H9; inversion H22.
  (* (be, mem) >- true *)
  - apply (XWhileT mem mem'1 mem' be ins); auto. rewrite <- H25. auto.
  (* (be, mem) >- false *)
  - inversion H16. rewrite <- H25. auto. 
Qed.

(* 7.6 *)
Lemma repeat_plus_one : forall mem mem' n ins,
    (BEGIN ins; REPEAT n # ins; END, mem) >> mem'
    -> (REPEAT S n# ins, mem) >> mem'.
Proof.
  intros. inversion H. inversion H1. inversion H9. 
  apply XRepeatS with (mem' := mem'1).
  + auto.
  + inversion H15. rewrite <- H18. auto. 
Qed.

(* 7.7 *)
Require Import Coq.Arith.Plus.

Lemma repeat_seq : forall n m mem mem' mem'' ins,
    (REPEAT n # ins, mem) >> mem'
    -> (REPEAT m # ins, mem') >> mem''
    -> (REPEAT n+m # ins, mem) >> mem''.
Proof.
  induction n; intros; simpl; inversion H; auto.
  apply XRepeatS with (mem' := mem'0); auto.
  apply IHn with (mem' := mem'); auto.
Qed.

(* 7.8 *)
Lemma update_const : forall mem v1 v2,
    v2 <> v1 -> lookup v1 (update v2 false (update v1 true mem))
                = lookup v1 (update v1 true mem).
Proof.
  intros. unfold lookup. unfold update.
  elim (beq_nat_false_iff v2 v1). intros. apply H1 in H. rewrite H.
  elim (beq_nat_refl v1). unfold lookup. elim (beq_nat_refl v1).
  auto.
Qed.

Lemma PP_v1_v2 : forall mem mem' v1 v2,
    v2 <> v1
    -> (BEGIN v1 ::= TRUE; v2 ::= ¬ VAR v1; END, mem) >> mem'
    -> (VAR v2, mem') >- false /\ (VAR v1, mem') >- true.
Proof.
  intros mem mem' v1 v2 diff prog. inversion prog.

  (* v1 := true; *)
  inversion H0.

  (* v2 := ~ VAR v1; *)
  inversion H5. inversion H13.
  rewrite <- H16 in H12. rewrite <- H12 in H8. inversion H8.

  (* EMPTY *)
  inversion H18. inversion H26.
  - rewrite <- H30 in H25. rewrite <- H25 in H21. inversion H21. split.
    + rewrite <- (lookup_update (update v1 true mem) v2 false) at 2. constructor.  
    + rewrite <- (lookup_update mem v1 true) at 2.
      apply (update_const mem v1 v2) in diff. rewrite <- diff. constructor.
  - rewrite <- H30 in H25.
    inversion H28. unfold lookup in H34. unfold update in H34.
    rewrite <- (beq_nat_refl v1) in H34. discriminate.
Qed.