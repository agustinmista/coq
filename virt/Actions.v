(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Require Import State.

Parameter ctxt : context.

(* stolen from http://adam.chlipala.net/cpdt/html/Match.html *)
Ltac notHyp P :=
  match goal with
  | [ _ : P |- _ ] => fail 1
  | _ =>
    match P with
    | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
    | _ => idtac
    end
  end.

Ltac extend pf :=
  let t := type of pf in
  notHyp t; generalize pf; intro.

Ltac completer :=
  repeat
    match goal with
    | [ |- _ /\ _ ] => constructor
    | [ H : ?P /\ ?Q |- _ ] =>
      destruct H; repeat
        match goal with
        | [ H' : P /\ Q |- _ ] => clear H'
        end
    | [ H : ?P -> _, H' : ?P |- _ ] => specialize (H H')
    | [ |- forall x, _ ] => intro
    | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
    end.

Ltac elim_clear H := elim H; clear H; intros.


Section Actions.
  
  Inductive Action :=
  | read : vadd -> Action
  | write : vadd -> value -> Action
  | chmod : Action.

  (* Action preconditions *)
  (* read and write share the same precondition using disjunctive patterns *)
  Definition Pre (s : State) (a : Action) : Prop :=
    match a with
    | read va | write va _ =>
      ctxt_vadd_accessible ctxt va = true
      /\ aos_activity s = running
      /\ exists (ma : madd) (p : page),
           va_mapped_to_ma s va ma
           /\ memory s ma = Some p
           /\ is_RW (page_content p)
    | chmod => 
      aos_activity s = waiting
      /\ exists (curr_os : os),
          oss s (active_os s) = Some curr_os            
          /\ hcall curr_os = None
    end.

  (* Action postconditions *)
  Definition Post (s : State) (a : Action) (s' : State) : Prop :=
    match a with
    | read va =>
      s' = s
    | write va val =>
      exists (ma : madd),
        va_mapped_to_ma s va ma
        /\ memory s' = update (memory s) ma
                              (mk_page (RW (Some val)) (Os (active_os s)))
        /\ (forall (ma' : madd), ma <> ma' -> memory s' ma' = memory s ma')
        /\ active_os s = active_os s'
        /\ aos_exec_mode s = aos_exec_mode s'
        /\ aos_activity s = aos_activity s'
        /\ oss s = oss s'
        /\ hypervisor s = hypervisor s'
    | chmod =>
      (trusted_os ctxt s /\ aos_exec_mode s = usr /\ aos_exec_mode s' = svc \/
      ~trusted_os ctxt s /\ aos_exec_mode s = svc /\ aos_exec_mode s' = usr)
      /\ active_os s = active_os s'
      /\ aos_activity s = waiting
      /\ aos_activity s' = running
      /\ oss s = oss s'
      /\ hypervisor s = hypervisor s'
      /\ memory s = memory s'
    end.

  Definition valid_state_iii (s : State) : Prop :=
    ((trusted_os ctxt s /\ aos_activity s = running)    (* trusted os running *)
     \/ aos_activity s = waiting)                       (* hypervisor running *)
    -> aos_exec_mode s = svc.

  Definition inyective {A B : Set} (pmap : A ⇸ B) :=
    forall x y, pmap x = pmap y -> x = y.

  Definition valid_state_v (s : State) : Prop :=
    forall (o : os_ident) (pa : padd),
    exists (ma : madd) (p : page) (ph_map : padd ⇸ madd),
      hypervisor s o = Some ph_map
      /\ ph_map pa = Some ma
      /\ memory s ma = Some p
      /\ page_owned_by p = Os o
      /\ inyective ph_map.

  Definition valid_state_vi (s : State) : Prop :=
    forall (o : os_ident) (pt : page),
    exists (va_map : vadd ⇸ madd),
      page_content pt = PT va_map
      /\ page_owned_by pt = Os o
      /\ forall (va : vadd) (ma : madd),
         exists (p : page),
           va_map va = Some ma
           /\ memory s ma = Some p
           /\ ((ctxt_vadd_accessible ctxt va = true
                /\ page_owned_by p = Os o)
                \/ (ctxt_vadd_accessible ctxt va = false
                    /\ page_owned_by p = Hyp)).
  
  Definition valid_state (s : State) : Prop :=
    valid_state_iii s /\ valid_state_v s /\ valid_state_vi s.
  
  Inductive one_step : State -> Action -> State -> Prop :=
    one_step_ : forall (s s': State) (a: Action),
      valid_state s -> Pre s a -> Post s a s' -> one_step s a s'.

  Notation "a ⇒ s ↪ s'" := (one_step s a s') (at level 50).


  Theorem one_step_preserves_prop_iii : forall (s s' : State) (a : Action),
      a ⇒ s ↪ s' -> valid_state_iii s'.
  Proof.
    intros. inversion H. inversion H0. destruct a.
    (* a = read v *)
    - inversion H2. auto.
    (* a = write v v0 *)
    - inversion H1. inversion H2.
      unfold valid_state_iii, trusted_os in *. completer.
      rewrite <- H14. apply H6.
      rewrite <- H13 in H20. rewrite <- H15 in H20. auto.
    (* a = chmod *)
    - inversion H1. inversion H2.
      unfold valid_state_iii, trusted_os in *.
      elim H10; completer; auto. elim_clear H21.
      + elim_clear H21. rewrite H11 in H18. contradiction.
      + rewrite H21 in H13. discriminate.
  Qed. 


  Theorem read_isolation : forall (s s' : State) (va : vadd),
      read va ⇒ s ↪ s'
      -> exists (ma : madd),
        va_mapped_to_ma s va ma
        /\ exists (p : page),
          memory s ma = Some p
          /\ page_owned_by p = Os (active_os s).
  Proof.
    intros. inversion_clear H. inversion H1. inversion H2. completer.
    
    elim_clear H5. elim_clear H5. completer.

    exists x. split; auto.
    exists x0. split; auto.

    unfold valid_state, valid_state_vi in *. completer.

    elim (H9 (active_os s) x0). clear H9. intros.
    elim_clear H9. completer. auto.
  Qed.

End Actions.