(*******************************************************************
 * Este archivo especifica el estado.
 * 
 ******************************************************************)

(* Shortcut notation for partial functions *)
Definition partial a b := a -> option b.
Notation "a ⇸ b" := (partial a b) (at level 51, right associativity).

Section State.

  (** Identificadores de OSs e Hypercalls *)
  Parameter os_ident : Set.
  Parameter os_ident_eq : forall oi1 oi2 : os_ident, {oi1 = oi2} + {oi1 <> oi2}.

  Parameter Hyperv_call : Set.

  (* Memoria y direcciones *)

  (** Direcciones Virtuales. **)
  Parameter vadd : Set.
  Parameter vadd_eq : forall va1 va2 : vadd, {va1 = va2} + {va1 <> va2}.

  (** Direcciones de Máquina. **)
  Parameter madd :  Set.
  Parameter madd_eq : forall ma1 ma2 : madd, {ma1 = ma2} + {ma1 <> ma2}.

  (** Direcciones Físicas **)
  Parameter padd : Set.
  Parameter padd_eq : forall pa1 pa2 : padd, {pa1 = pa2} + {pa1 <> pa2}.

  (** Memory values. **)
  Parameter value : Set.
  Parameter value_eq : forall val1 val2 : value, {val1 = val2} + {val1 <> val2}.


  (* Environment *)
  Record context : Set :=
    Context {
        (** una dirección virtual es accesible, no está reserveda por el HV **)
        ctxt_vadd_accessible: vadd -> bool;
        (** guest Oss (Confiable/No Confiable) **)
        ctxt_oss : os_ident -> bool
      }.
  

  (* Operative Systems *)
  Record os := mk_os { curr_page : padd; hcall : option Hyperv_call }.

  Definition oss_map := os_ident ⇸ os.


  (* Execution Modes *)
  Inductive exec_mode := usr | svc.
  Inductive os_activity := running | waiting.


  (* Memory Mappings *)
  Definition hypervisor_map := os_ident ⇸ padd ⇸ madd.

  Inductive content :=
  | RW (v : option value)
  | PT (va_to_ma : vadd ⇸ madd)
  | Other.

  Definition is_RW c :=
    match c with
    | RW _ => True
    | _ => False
    end.

  Inductive page_owner :=
  | Hyp
  | Os (osi : os_ident)
  | No_Owner.

  Record page := mk_page { page_content : content; page_owned_by : page_owner }.

  Definition system_memory := madd ⇸ page.

  Definition update mem addr page : system_memory :=
    fun addr' => if madd_eq addr' addr
                 then Some page
                 else mem addr'.
 

  (* States *)
  Record State :=
    mk_State {
        active_os : os_ident;
        aos_exec_mode : exec_mode;
        aos_activity : os_activity;
        oss : oss_map;
        hypervisor : hypervisor_map;
        memory : system_memory
      }.

  
  Definition va_mapped_to_ma (s : State) (va : vadd) (ma : madd) :=
    exists (curr_os : os)           (* SO actual *)        
           (ph_map : padd ⇸ madd)  (* mappings del HV para el SO actual *)
           (curr_pt_addr : madd)    (* dirección  de la PT del SO actual *)
           (pt : page)              (* PT del SO actual *)
           (vt_map : vadd ⇸ madd), (* mappings de la PT del SO actual *)
      oss s (active_os s) = Some curr_os            
      /\ hypervisor s (active_os s) = Some ph_map    
      /\ ph_map (curr_page curr_os) = Some curr_pt_addr
      /\ memory s curr_pt_addr = Some pt
      /\ page_content pt = PT vt_map
      /\ vt_map va = Some ma.

  Definition trusted_os (ctxt : context) (s : State) : Prop :=
    ctxt_oss ctxt (active_os s) = true. 

End State.
