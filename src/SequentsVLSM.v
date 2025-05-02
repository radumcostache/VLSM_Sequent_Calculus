From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude.
From VLSM.Lib Require Import ListExtras.
From VLSM.Core Require Import VLSMProjections.
From VLSM.Core Require Import VLSM Composition ProjectionTraces.
From VLSM_SC Require Import Sequents.

Require Import Coq.Lists.List.
Require Import Wellfounded.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Lt.
 

Import Form.
Import Calculus.

(** * Sequent Calculus VLSMs *)

Section sec_sequent_calculus.

#[local] Notation "⊤" := FTop.
#[local] Notation "⊥" := FBot.
#[local] Notation "x ∨ y" := (FDisj x y) (at level 85, right associativity).
#[local] Notation "x ∧ y" := (FConj x y) (at level 80, right associativity).
#[local] Notation "x → y" := (FImpl x y) (at level 99, y at level 200, right associativity).


(** * Encoding Sequents *)


Inductive RecEmitLabel : Type := 
| rec
| emit.

Inductive RecEmitLeftRight : Type :=
| recLeft  
| recRight
| emitLeft 
| emitRight.

Inductive XCHGLabel : Type := 
| recX
| extract
| exchangeEmit.


(** Define the structure of sequents: a pair of lists of formulas. *)


Definition seq_left (s : Sequent) : list Formula :=
  match s with
  | seq Gamma _ => Gamma
  end.

Definition seq_right (s : Sequent) : list Formula :=
  match s with
  | seq _ Delta => Delta
  end.

(** * VLSM for the Identity Rule *)

(** Labels for the identity rule transitions are formulas. *)
Definition V_ID_label := Formula.

(** States are unit *)
Definition V_ID_state := unit.

Definition V_ID_vlsm_type : VLSMType Sequent :=
  {| label := V_ID_label;
     state := V_ID_state; |}.

(** Transition function for the identity rule. *)


Definition V_ID_machine : VLSMMachine V_ID_vlsm_type :=
  {| initial_state_prop := fun _ => True;
     s0 :=  populate (exist _ () I);
     initial_message_prop := fun _ => False;
     transition := fun l _ => ((), Some (seq [l] [l]));
     valid := fun _ som => som.2 = None |}.

Definition V_ID : VLSM Sequent :=
  mk_vlsm V_ID_machine.

  (** * VLSM for the Bottom Rule *)

(** Labels for the bottom rule transitions are unit. *)
Definition V_BOT_label := unit.

(** States are unit. *)
Definition V_BOT_state := unit.

Definition V_BOT_vlsm_type : VLSMType Sequent :=
  {| label := V_BOT_label;
     state := V_BOT_state; |}.

(** Transition function for the bottom rule. *)
Definition V_BOT_machine : VLSMMachine V_BOT_vlsm_type :=
  {| initial_state_prop := fun _ => True;
     s0 := populate (exist _ () I);
     initial_message_prop := fun _ => False;
     transition := fun _ _ => ((), Some (seq [⊥] []));
     (* Might change it later *)
     valid := fun _ som => som.2 = None |}.

Definition V_BOT : VLSM Sequent :=
  mk_vlsm V_BOT_machine.

  (** * VLSM for the Top Rule *)

(** Labels for the bottom rule transitions are unit. *)
Definition V_TOP_label := unit.

(** States are unit. *)
Definition V_TOP_state := unit.

Definition V_TOP_vlsm_type : VLSMType Sequent :=
  {| label := V_TOP_label;
     state := V_TOP_state; |}.

(* TODO: Check if we cannot abstract the TOP/BOT machines as in Formulas.v *)
Definition V_TOP_machine : VLSMMachine V_TOP_vlsm_type :=
  {| initial_state_prop := fun _ => True;
     s0 := populate (exist _ () I);
     initial_message_prop := fun _ => False;
     transition := fun _ _ => ((), Some (seq [] [⊤]));
     (* Might change it later *)
     valid := fun _ som =>  som.2 = None |}.

Definition V_TOP : VLSM Sequent :=
  mk_vlsm V_TOP_machine.

Definition V_IMP_RIGHT_label := unit.
Definition V_IMP_RIGHT_state := unit.

Definition V_IMP_RIGHT_vlsm_type : VLSMType Sequent :=
  {| label := V_IMP_RIGHT_label;
     state := V_IMP_RIGHT_state; |}.

Definition V_IMP_RIGHT_machine : VLSMMachine V_IMP_RIGHT_vlsm_type :=
  {| initial_state_prop := fun _ => True;
     s0 := populate (exist _ () I);
     initial_message_prop := fun _ => False;
     transition := fun _ som =>
       match som.2 with
       | Some (seq (A :: Gamma) (B :: Delta)) =>
           ((), Some (seq Gamma ((FImpl A B) :: Delta)))
       | _ => ((), None)
       end;
     valid := fun _ som => 
       match som.2 with 
       | Some (seq (A :: Gamma) (B :: Delta)) => True
       | _ => False
       end; |}.
Definition V_IMP_RIGHT : VLSM Sequent :=
    mk_vlsm V_IMP_RIGHT_machine.

(** Labels for the conjunction left rule transitions are unit. *)
Definition V_CONJ_LEFT_1_label := Formula.

(** States are unit. *)
Definition V_CONJ_LEFT_1_state := unit.

Definition V_CONJ_LEFT_1_vlsm_type : VLSMType Sequent :=
  {| label := V_CONJ_LEFT_1_label;
     state := V_CONJ_LEFT_1_state; |}.

(** Transition function for the conjunction left rule. *)
Definition V_CONJ_LEFT_1_machine : VLSMMachine V_CONJ_LEFT_1_vlsm_type :=
  {| initial_state_prop := fun _ => True;
     s0 := populate (exist _ () I);
     initial_message_prop := fun _ => False;
     transition := fun B som =>
       match som.2 with
       | Some (seq (A :: Gamma) Delta) =>
           ((), Some (seq ((FConj A B) :: Gamma) Delta))
       | _ => ((), None)
       end;
     valid := fun _ som =>        
       match som.2 with
       | Some (seq (A :: Gamma) Delta) => True
       | _ => False
       end; |}.

Definition V_CONJ_LEFT_1 : VLSM Sequent :=
  mk_vlsm V_CONJ_LEFT_1_machine.

(** Labels for the conjunction left rule transitions are unit. *)
Definition V_CONJ_LEFT_2_label := Formula.

(** States are unit. *)
Definition V_CONJ_LEFT_2_state := unit.

Definition V_CONJ_LEFT_2_vlsm_type : VLSMType Sequent :=
  {| label := V_CONJ_LEFT_2_label;
     state := V_CONJ_LEFT_2_state; |}.

(** Transition function for the conjunction left rule. *)
Definition V_CONJ_LEFT_2_machine : VLSMMachine V_CONJ_LEFT_2_vlsm_type :=
  {| initial_state_prop := fun _ => True;
     s0 := populate (exist _ () I);
     initial_message_prop := fun _ => False;
     transition := fun B som =>
       match som.2 with
       | Some (seq (A :: Gamma) Delta) =>
           ((), Some (seq ((FConj B A) :: Gamma) Delta))
       | _ => ((), None)
       end;
     valid := fun _ som => 
      match som.2 with
       | Some (seq (A :: Gamma) Delta) => True
       | _ => False
       end; |}.

Definition V_CONJ_LEFT_2 : VLSM Sequent :=
  mk_vlsm V_CONJ_LEFT_2_machine.
(** Labels for the conjunction right rule transitions are unit. *)
Definition V_CONJ_RIGHT_label := RecEmitLabel.

(** States are unit. *)
Definition V_CONJ_RIGHT_state := option Sequent.

Definition V_CONJ_RIGHT_vlsm_type : VLSMType Sequent :=
  {| label := V_CONJ_RIGHT_label;
     state := V_CONJ_RIGHT_state; |}.

(** Transition function for the conjunction right rule. *)

Definition V_CONJ_RIGHT_machine : VLSMMachine V_CONJ_RIGHT_vlsm_type :=
  {| initial_state_prop := fun s => s = None;
     s0 := populate (exist _ None eq_refl); (* Initial state with empty Gamma and Delta *)
     initial_message_prop := fun _ => False;
     transition := fun l '(st, msg) =>
        match l, st, msg with 
        | rec, None, Some (seq Gamma (A :: Delta)) => (Some (seq Gamma (A :: Delta)), None)
        | emit, Some (seq Gamma (A :: Delta)), Some (seq Gamma' (B :: Delta')) =>
            if list_formula_eq Gamma Gamma' && list_formula_eq Delta Delta' then
              (None, Some (seq Gamma (FConj A  B :: Delta)))
            else
              (None, None)
        | _, _, _ => (None, None) 
        end;
     valid := fun l som =>       
      match l, som.1, som.2 with 
        | rec, None, Some (seq Gamma (A :: Delta)) => True
        | emit, Some (seq Gamma (A :: Delta)), Some (seq Gamma' (B :: Delta')) => True
        | _, _, _ => False 
        end; |}.


Definition V_CONJ_RIGHT : VLSM Sequent :=
  mk_vlsm V_CONJ_RIGHT_machine.

(** Labels for the disjunction left rule transitions are unit. *)
Definition V_DISJ_LEFT_label := RecEmitLabel.

(** States are unit. *)
Definition V_DISJ_LEFT_state := option Sequent.

Definition V_DISJ_LEFT_vlsm_type : VLSMType Sequent :=
  {| label := V_DISJ_LEFT_label;
     state := V_DISJ_LEFT_state; |}.

(** Transition function for the disjunction left rule. *)
Definition V_DISJ_LEFT_machine : VLSMMachine V_DISJ_LEFT_vlsm_type :=
  {| initial_state_prop := fun s => s = None;
     s0 := populate (exist _ None eq_refl);
     initial_message_prop := fun _ => False;
     transition := fun l '(st, msg) =>
       match l, st, msg with
       | rec, None, Some (seq (A :: Gamma) Delta) =>
           (Some (seq (A :: Gamma) Delta), None)
       | emit, Some (seq (A :: Gamma) Delta), Some (seq (B :: Gamma') Delta') =>
              if list_formula_eq Gamma Gamma' && list_formula_eq Delta Delta' then
                 (None, Some (seq (FDisj A B :: Gamma) Delta))
              else
                 (None, None)
       | _, _, _=> (None, None)
       end;
     valid := fun l som =>        
      match l, som.1, som.2 with
        | rec, None, Some (seq (A :: Gamma) Delta) => True
        | emit, Some (seq (A :: Gamma) Delta), Some (seq (B :: Gamma') Delta') =>
                if list_formula_eq Gamma Gamma' && list_formula_eq Delta Delta' then
                  True
                else
                  False
        | _, _, _=> False
      end; |}.

Definition V_DISJ_LEFT : VLSM Sequent :=
  mk_vlsm V_DISJ_LEFT_machine.

Definition V_DISJ_RIGHT_1_label := Formula.

(** States are unit. *)
Definition V_DISJ_RIGHT_1_state := unit.

Definition V_DISJ_RIGHT_1_vlsm_type : VLSMType Sequent :=
  {| label := V_DISJ_RIGHT_1_label;
     state := V_DISJ_RIGHT_1_state; |}.

(** Transition function for the disjunction right rule. *)
Definition V_DISJ_RIGHT_1_machine : VLSMMachine V_DISJ_RIGHT_1_vlsm_type :=
  {| initial_state_prop := fun _ => True;
     s0 := populate (exist _ () I);
     initial_message_prop := fun _ => False;
     transition := fun B som =>
       match som.2 with
       | Some (seq Gamma (A :: Delta)) =>
           ((), Some (seq Gamma (FDisj A B :: Delta)))
       | _ => ((), None)
       end;
     valid := fun l som => 
      match som.2 with
       | Some (seq Gamma (A :: Delta)) => True
       | _ => False
       end; |}.

Definition V_DISJ_RIGHT_1 : VLSM Sequent :=
  mk_vlsm V_DISJ_RIGHT_1_machine.

Definition V_DISJ_RIGHT_2_label := Formula.

(** States are unit. *)
Definition V_DISJ_RIGHT_2_state := unit.

Definition V_DISJ_RIGHT_2_vlsm_type : VLSMType Sequent :=
  {| label := V_DISJ_RIGHT_2_label;
     state := V_DISJ_RIGHT_2_state; |}.

(** Transition function for the disjunction right rule. *)
Definition V_DISJ_RIGHT_2_machine : VLSMMachine V_DISJ_RIGHT_2_vlsm_type :=
  {| initial_state_prop := fun _ => True;
     s0 := populate (exist _ () I);
     initial_message_prop := fun _ => False;
     transition := fun B som =>
       match som.2 with
       | Some (seq Gamma (A :: Delta)) =>
           ((), Some (seq Gamma (FDisj B A :: Delta)))
       | _ => ((), None)
       end;
     valid := fun _ som =>
      match som.2 with
       | Some (seq Gamma (A :: Delta)) => True
       | _ => False
       end; |}.

Definition V_DISJ_RIGHT_2 : VLSM Sequent :=
  mk_vlsm V_DISJ_RIGHT_2_machine.

Definition V_WK_LEFT_state := unit.
Definition V_WK_LEFT_label := Formula.

Definition V_WK_LEFT_vlsm_type : VLSMType Sequent :=
  {| label := V_WK_LEFT_label;
     state := V_WK_LEFT_state; |}.
Definition V_WK_LEFT_machine : VLSMMachine V_WK_LEFT_vlsm_type :=
    {| initial_state_prop := fun _ => True;
         s0 := populate (exist _ () I);
         initial_message_prop := fun _ => False;
         transition := fun A som =>
         match som.2 with
         | Some (seq Gamma Delta) =>
             ((), Some (seq (A :: Gamma) Delta))
         | _ => ((), None)
         end;
         valid := fun _ som => 
         match som.2 with
         | Some (seq Gamma Delta) => True
         | _ => False
         end; |}.
Definition V_WK_LEFT : VLSM Sequent :=
    mk_vlsm V_WK_LEFT_machine.

Definition V_WK_RIGHT_state := unit.
Definition V_WK_RIGHT_label := Formula.

Definition V_WK_RIGHT_vlsm_type : VLSMType Sequent :=
  {| label := V_WK_RIGHT_label;
     state := V_WK_RIGHT_state; |}.
Definition V_WK_RIGHT_machine : VLSMMachine V_WK_RIGHT_vlsm_type :=
    {| initial_state_prop := fun _ => True;
         s0 := populate (exist _ () I);
         initial_message_prop := fun _ => False;
         transition := fun A som =>
         match som.2 with
         | Some (seq Gamma Delta) =>
             ((), Some (seq Gamma (A :: Delta)))
         | _ => ((), None)
         end;
         valid := fun _ som => 
        match som.2 with
         | Some (seq Gamma Delta) => True
         | _ => False
         end; |}.
Definition V_WK_RIGHT : VLSM Sequent :=
    mk_vlsm V_WK_RIGHT_machine.

Definition V_CT_LEFT_state := unit.
Definition V_CT_LEFT_label := unit.

Definition V_CT_LEFT_vlsm_type : VLSMType Sequent :=
  {| label := V_CT_LEFT_label;
     state := V_CT_LEFT_state; |}.
Definition V_CT_LEFT_machine : VLSMMachine V_CT_LEFT_vlsm_type :=
    {| initial_state_prop := fun _ => True;
         s0 := populate (exist _ () I);
         initial_message_prop := fun _ => False;
         transition := fun _ som =>
         match som.2 with
         | Some (seq (A :: B :: Gamma) Delta) =>
            if decide (A = B) then ((), Some (seq (A :: Gamma) Delta))
            else ((), None)
         | _ => ((), None)
         end;
         valid := fun _ som => 
        match som.2 with
         | Some (seq (A :: B :: Gamma) Delta) =>
            if decide (A = B) then True
            else False 
         | _ => False
         end; |}.
Definition V_CT_LEFT : VLSM Sequent :=
    mk_vlsm V_CT_LEFT_machine.

Definition V_CT_RIGHT_state := unit.
Definition V_CT_RIGHT_label := unit.

Definition V_CT_RIGHT_vlsm_type : VLSMType Sequent :=
  {| label := V_CT_RIGHT_label;
     state := V_CT_RIGHT_state; |}.

Definition V_CT_RIGHT_machine : VLSMMachine V_CT_RIGHT_vlsm_type :=
    {| initial_state_prop := fun _ => True;
         s0 := populate (exist _ () I);
         initial_message_prop := fun _ => False;
         transition := fun _ som =>
         match som.2 with
         | Some (seq Gamma (A :: B :: Delta)) =>
            if decide (A = B) then ((), Some (seq Gamma (A :: Delta)))
            else ((), None)
         | _ => ((), None)
         end;
         valid := fun _ som => 
         match som.2 with
         | Some (seq Gamma (A :: B :: Delta)) =>
            if decide (A = B) then True
            else False
         | _ => False
         end; |}.

Definition V_CT_RIGHT : VLSM Sequent :=
    mk_vlsm V_CT_RIGHT_machine.

Definition V_IMP_LEFT_label := RecEmitLeftRight.
Definition V_IMP_LEFT_state := option Sequent.

Definition V_IMP_LEFT_vlsm_type : VLSMType Sequent :=
  {| label := V_IMP_LEFT_label;
     state := V_IMP_LEFT_state; |}.

(** Transition function for the implication left rule. *)
Definition V_IMP_LEFT_machine : VLSMMachine V_IMP_LEFT_vlsm_type :=
  {| initial_state_prop := fun s => s = None;
     s0 := populate (exist _ None eq_refl);
     initial_message_prop := fun _ => False;

     transition := fun l som =>
       match l, som.1, som.2 with
       | recLeft, None, Some (seq (B :: Gamma) Delta) =>
           (Some (seq (B :: Gamma) Delta), None)
       | recRight, None, Some (seq Gamma (A :: Delta)) =>
           (Some (seq Gamma (A :: Delta)), None)
       | emitLeft, Some (seq (B :: Gamma') Delta'), Some (seq Gamma (A :: Delta)) =>
           (None, Some (seq (FImpl A B :: Gamma ++ Gamma') (Delta ++ Delta')))
       | emitRight, Some (seq Gamma (A :: Delta)), Some (seq (B :: Gamma') Delta') =>
           (None, Some (seq (FImpl A B :: Gamma ++ Gamma') (Delta ++ Delta')))
       | _, _, _ => (None, None)
       end;

     valid := fun l som =>
       match l, som.1, som.2 with
       | recLeft, None, Some (seq (B :: Gamma) Delta) => True
       | recRight, None, Some (seq Gamma (A :: Delta)) => True
       | emitLeft, Some (seq (B :: Gamma') Delta'), Some (seq Gamma (A :: Delta)) => True
       | emitRight, Some (seq Gamma (A :: Delta)), Some (seq (B :: Gamma') Delta') => True
       | _, _, _ => False
       end; |}.

Definition V_IMP_LEFT : VLSM Sequent :=
  mk_vlsm V_IMP_LEFT_machine.

Definition V_CUT_label := RecEmitLeftRight.
Definition V_CUT_state := option Sequent.

Definition V_CUT_vlsm_type : VLSMType Sequent :=
  {| label := V_CUT_label;
     state := V_CUT_state; |}.

(** Transition function for the cut rule. *)
Definition V_CUT_machine : VLSMMachine V_CUT_vlsm_type :=
  {| initial_state_prop := fun s => s = None;
     s0 := populate (exist _ None eq_refl);
     initial_message_prop := fun _ => False;

     transition := fun l som =>
       match l, som.1, som.2 with
       | recLeft, None, Some (seq (A :: Γ) Δ) =>
           (Some (seq (A :: Γ) Δ), None)
       | recRight, None, Some (seq Γ (A :: Δ)) =>
           (Some (seq Γ (A :: Δ)), None)
       | emitLeft, Some (seq (A :: Gamma) Delta), Some (seq Gamma' (A' :: Delta')) =>
           if decide (A = A') then (None, Some (seq (Gamma ++ Gamma') (Delta ++ Delta')))
           else (None, None)
       | emitRight, Some (seq Gamma' (A :: Delta')), Some (seq (A' :: Gamma) Delta) =>
           if decide (A = A') then (None, Some (seq (Gamma ++ Gamma') (Delta ++ Delta')))
           else (None, None)
       | _, _, _ => (None, None)
       end;

     valid := fun l som =>
       match l, som.1, som.2 with
       | recLeft, None, Some (seq (A :: Γ) Δ) => True
       | recRight, None, Some (seq Γ (A :: Δ)) => True
       | emitLeft, Some (seq (A :: Gamma) Delta), Some (seq Gamma' (A' :: Delta')) => 
            if decide (A = A') then True 
            else False
       | emitRight, Some (seq Gamma' (A :: Delta')), Some (seq (A' :: Gamma) Delta) =>
            if decide (A = A') then True 
            else False
       | _, _, _ => False
       end; |}.
Definition V_CUT : VLSM Sequent :=
    mk_vlsm V_CUT_machine.


Definition V_XCHG_LEFT_label := XCHGLabel.
Definition V_XCHG_LEFT_state := prod (list Formula) (option Sequent).

Definition V_XCHG_LEFT_vlsm_type : VLSMType Sequent :=
  {| label := V_XCHG_LEFT_label;
     state := V_XCHG_LEFT_state; |}.

Definition V_XCHG_LEFT_machine : VLSMMachine V_XCHG_LEFT_vlsm_type := 
  {| initial_state_prop := fun s => s = ([], None);
     s0 := populate (exist _ ([], None) eq_refl);
     initial_message_prop := fun _ => False;

     transition := fun l som =>
       match l, som.1, som.2 with
       | recX, ([], None), Some (seq Γ Δ) => (([], Some (seq Γ Δ)), None)
       | extract, (Γ, Some (seq (A :: Π) Δ)), None => ((Γ ++ [A], Some (seq Π Δ)), None)
       | exchangeEmit, (Γ, Some (seq (B :: C :: Π) Δ)), None => (([], None), Some (seq (Γ ++ C :: B :: Π) Δ))
       | _, _, _ => (([], None), None)
       end;

     valid := fun l som =>
       match l, som.1, som.2 with
       | recX, ([], None), Some (seq Γ Δ) => True
       | extract, (Γ, Some (seq (A :: Π) Δ)), None => True
       | exchangeEmit, (Γ, Some (seq (B :: C :: Π) Δ)), None => True
       | _, _, _ => False
       end; |}.

Definition V_XCHG_LEFT : VLSM Sequent := 
  mk_vlsm V_XCHG_LEFT_machine.

Definition V_XCHG_RIGHT_label := XCHGLabel.
Definition V_XCHG_RIGHT_state := prod (list Formula) (option Sequent).

Definition V_XCHG_RIGHT_vlsm_type : VLSMType Sequent :=
  {| label := V_XCHG_RIGHT_label;
     state := V_XCHG_RIGHT_state; |}.

Definition V_XCHG_RIGHT_machine : VLSMMachine V_XCHG_RIGHT_vlsm_type := 
  {| initial_state_prop := fun s => s = ([], None);
     s0 := populate (exist _ ([], None) eq_refl);
     initial_message_prop := fun _ => False;

     transition := fun l som =>
       match l, som.1, som.2 with
       | recX, ([], None), Some (seq Γ Δ) => (([], Some (seq Γ Δ)), None)
       | extract, (Γ, Some (seq Δ (A :: Π) )), None => ((Γ ++ [A], Some (seq Δ Π)), None)
       | exchangeEmit, (Γ, Some (seq Δ (B :: C :: Π))), None => (([], None), Some (seq Δ (Γ ++ C :: B :: Π)))
       | _, _, _ => (([], None), None)
       end;

     valid := fun l som => 
       match l, som.1, som.2 with
       | recX, ([], None), Some (seq Γ Δ) => True
       | extract, (Γ, Some (seq Δ (A :: Π) )), None => True
       | exchangeEmit, (Γ, Some (seq Δ (B :: C :: Π))), None => True
       | _, _, _ => False
       end;
       |}.

Definition V_XCHG_RIGHT : VLSM Sequent := 
  mk_vlsm V_XCHG_RIGHT_machine.

Inductive sequent_index : Type :=
| I_V_ID
| I_V_BOT
| I_V_TOP
| I_V_IMP_RIGHT
| I_V_IMP_LEFT
| I_V_CONJ_LEFT_1
| I_V_CONJ_LEFT_2
| I_V_CONJ_RIGHT
| I_V_DISJ_LEFT
| I_V_DISJ_RIGHT_1
| I_V_DISJ_RIGHT_2
| I_V_WK_LEFT
| I_V_WK_RIGHT
| I_V_CT_LEFT
| I_V_CT_RIGHT
(* | I_V_CUT *)
| I_V_XCHG_LEFT
| I_V_XCHG_RIGHT.

#[export] Instance index_dec : EqDecision sequent_index.
Proof. by intros ? ?; unfold Decision; decide equality. Qed.

Definition sequent_vlsm_components (i : sequent_index) : VLSM Sequent :=
    match i with
    | I_V_ID => V_ID
    | I_V_BOT => V_BOT
    | I_V_TOP => V_TOP
    | I_V_IMP_RIGHT => V_IMP_RIGHT
    | I_V_IMP_LEFT => V_IMP_LEFT
    | I_V_CONJ_LEFT_1 => V_CONJ_LEFT_1
    | I_V_CONJ_LEFT_2 => V_CONJ_LEFT_2
    | I_V_CONJ_RIGHT => V_CONJ_RIGHT
    | I_V_DISJ_LEFT => V_DISJ_LEFT
    | I_V_DISJ_RIGHT_1 => V_DISJ_RIGHT_1
    | I_V_DISJ_RIGHT_2 => V_DISJ_RIGHT_2
    | I_V_WK_LEFT => V_WK_LEFT
    | I_V_WK_RIGHT => V_WK_RIGHT
    | I_V_CT_LEFT => V_CT_LEFT
    | I_V_CT_RIGHT => V_CT_RIGHT
    (* | I_V_CUT => V_CUT *)
    | I_V_XCHG_LEFT => V_XCHG_LEFT
    | I_V_XCHG_RIGHT => V_XCHG_RIGHT
    end.

Definition sequent_vlsm : VLSM Sequent :=
  free_composite_vlsm sequent_vlsm_components.

Lemma list_formula_eq_refl : forall (l : list Formula), list_formula_eq l l = true.
Proof.
  intros l.
  unfold list_formula_eq.
  destruct (decide (l = l)).
  - reflexivity.
  - contradiction.
Qed.

Definition vlsm_valid_sequent : Sequent -> Prop := 
  fun Sq => valid_message_prop sequent_vlsm (Sq).

Definition derivable_sequent : Sequent -> Prop := 
  fun Sq => exists (k : nat), SC_derivation k (Sq). 

Definition s0_seq := ` (composite_s0 sequent_vlsm_components).

Definition s_xchg_left (s : V_XCHG_LEFT_state) : (state sequent_vlsm) := 
  state_update sequent_vlsm_components s0_seq I_V_XCHG_LEFT s.

Lemma cons_eq_app : forall (A : Type) (h : A) (t : list A),
  h :: t = [h] ++ t.
Proof.
  intros. reflexivity.
Qed.

Lemma xchg_left_vlsm_capt : 
  forall (Π Γ Δ : list Formula) (A B : Formula), 
    vlsm_valid_sequent (seq (Γ ++ A :: B :: Δ) Π) -> 
      input_valid_transition sequent_vlsm (existT I_V_XCHG_LEFT recX) 
        (s0_seq, Some (seq (Γ ++ A :: B :: Δ) Π))
        ((s_xchg_left ([], Some (seq (Γ ++ A :: B :: Δ) Π))), None).
Proof.
  intros Π Γ Δ A B.
  intros H.
  unfold s0_seq.
  repeat split.
  - apply initial_state_is_valid. by destruct composite_s0.
  - by apply H.
Qed. 

Lemma xchg_left_vlsm_invariant : 
  forall (Γ Δ Π Σ: list Formula),
    valid_state_prop sequent_vlsm (state_update sequent_vlsm_components s0_seq I_V_XCHG_LEFT 
                (Σ, Some (seq (Γ ++ Δ) Π))) -> 
    valid_state_prop sequent_vlsm (state_update sequent_vlsm_components s0_seq I_V_XCHG_LEFT 
            (Σ ++ Γ, Some (seq Δ Π))).
Proof.
  intros Γ.
  induction Γ; intros Δ Π Σ H.
  - by rewrite app_nil_r.
  - rewrite cons_eq_app.
    rewrite app_assoc.
    apply IHΓ.
    cut (input_valid_transition sequent_vlsm (existT I_V_XCHG_LEFT extract) 
            (state_update sequent_vlsm_components s0_seq I_V_XCHG_LEFT (Σ, Some (seq ((a :: Γ) ++ Δ) Π)), None)
            (state_update sequent_vlsm_components s0_seq I_V_XCHG_LEFT (Σ ++ [a], Some (seq (Γ ++ Δ) Π)), None)
      );  [by eapply input_valid_transition_destination |].
      repeat split.
      + auto.
      + apply option_valid_message_None.
      + cbn. by rewrite state_update_eq.
      + cbn. rewrite state_update_eq.
        by rewrite state_update_twice.

Qed.

Lemma xchg_left_vlsm_final :
  forall (Γ Δ Π : list Formula) (A B : Formula),
    valid_state_prop sequent_vlsm (state_update sequent_vlsm_components s0_seq I_V_XCHG_LEFT 
        (Γ, Some (seq (A :: B :: Δ) Π))) -> 
          vlsm_valid_sequent (seq (Γ ++ B :: A :: Δ) Π).
Proof.
  intros Γ Δ Π A B.
  intros H.
  cut (input_valid_transition sequent_vlsm (existT I_V_XCHG_LEFT exchangeEmit) 
          (state_update sequent_vlsm_components s0_seq I_V_XCHG_LEFT (Γ, Some (seq (A :: B :: Δ) Π)), None)
          (s0_seq, Some (seq (Γ ++ B :: A :: Δ) Π))
  ); [by eapply input_valid_transition_out |].
  repeat split.
  - auto.
  - apply option_valid_message_None.
  - cbn. by rewrite state_update_eq.
  - cbn. rewrite state_update_eq. 
    rewrite state_update_twice.
    by rewrite state_update_id.
Qed. 

Lemma xchg_left_vlsm_valid : 
  forall (Π Γ Δ : list Formula) (A B : Formula), 
    vlsm_valid_sequent (seq (Γ ++ A :: B :: Δ) Π) -> 
      vlsm_valid_sequent (seq (Γ ++ B :: A :: Δ) Π).
Proof.
  intros Π Γ Δ A B. 
  intros H.
  apply xchg_left_vlsm_final.
  apply (xchg_left_vlsm_invariant Γ (A :: B :: Δ) Π []).
  remember (xchg_left_vlsm_capt _ _ _ _ _ H) as H1. 
  by eapply input_valid_transition_destination.

Qed.

Definition s_xchg_right (s : V_XCHG_RIGHT_state) : (state sequent_vlsm) := 
  state_update sequent_vlsm_components s0_seq I_V_XCHG_RIGHT s.

Lemma xchg_right_vlsm_capt : 
  forall (Π Γ Δ : list Formula) (A B : Formula), 
    vlsm_valid_sequent (seq Π (Γ ++ A :: B :: Δ)) -> 
      input_valid_transition sequent_vlsm (existT I_V_XCHG_RIGHT recX) 
        (s0_seq, Some (seq Π (Γ ++ A :: B :: Δ)))
        ((s_xchg_right ([], Some (seq Π (Γ ++ A :: B :: Δ)))), None).
Proof.
  intros Π Γ Δ A B.
  intros H.
  unfold s0_seq.
  repeat split.
  - apply initial_state_is_valid. by destruct composite_s0.
  - by apply H.
Qed. 

Lemma xchg_right_vlsm_invariant : 
  forall (Γ Δ Π Σ: list Formula),
    valid_state_prop sequent_vlsm (state_update sequent_vlsm_components s0_seq I_V_XCHG_RIGHT 
                (Σ, Some (seq Π (Γ ++ Δ)))) -> 
    valid_state_prop sequent_vlsm (state_update sequent_vlsm_components s0_seq I_V_XCHG_RIGHT 
            (Σ ++ Γ, Some (seq Π Δ))).
Proof.
  intros Γ.
  induction Γ; intros Δ Π Σ H.
  - by rewrite app_nil_r.
  - rewrite cons_eq_app.
    rewrite app_assoc.
    apply IHΓ.
    cut (input_valid_transition sequent_vlsm (existT I_V_XCHG_RIGHT extract) 
            (state_update sequent_vlsm_components s0_seq I_V_XCHG_RIGHT (Σ, Some (seq Π ((a :: Γ) ++ Δ))), None)
            (state_update sequent_vlsm_components s0_seq I_V_XCHG_RIGHT (Σ ++ [a], Some (seq Π (Γ ++ Δ))), None)
      );  [by eapply input_valid_transition_destination |].
      repeat split.
      + auto.
      + apply option_valid_message_None.
      + cbn. by rewrite state_update_eq.
      + cbn. rewrite state_update_eq.
        by rewrite state_update_twice.

Qed.

Lemma xchg_right_vlsm_final :
  forall (Γ Δ Π : list Formula) (A B : Formula),
    valid_state_prop sequent_vlsm (state_update sequent_vlsm_components s0_seq I_V_XCHG_RIGHT
        (Γ, Some (seq Π (A :: B :: Δ)))) -> 
          vlsm_valid_sequent (seq Π (Γ ++ B :: A :: Δ)).
Proof.
  intros Γ Δ Π A B.
  intros H.
  cut (input_valid_transition sequent_vlsm (existT I_V_XCHG_RIGHT exchangeEmit) 
          (state_update sequent_vlsm_components s0_seq I_V_XCHG_RIGHT (Γ, Some (seq Π (A :: B :: Δ))), None)
          (s0_seq, Some (seq Π (Γ ++ B :: A :: Δ)))
  ); [by eapply input_valid_transition_out |].
  repeat split.
  - auto.
  - apply option_valid_message_None.
  - cbn. by rewrite state_update_eq.
  - cbn. rewrite state_update_eq. 
    rewrite state_update_twice.
    by rewrite state_update_id.
Qed. 

Lemma xchg_right_vlsm_valid : 
  forall (Π Γ Δ : list Formula) (A B : Formula), 
    vlsm_valid_sequent (seq Π (Γ ++ A :: B :: Δ)) -> 
      vlsm_valid_sequent (seq Π (Γ ++ B :: A :: Δ)).
Proof.
  intros Π Γ Δ A B. 
  intros H.
  apply xchg_right_vlsm_final.
  apply (xchg_right_vlsm_invariant Γ (A :: B :: Δ) Π []).
  remember (xchg_right_vlsm_capt _ _ _ _ _ H) as H1. 
  by eapply input_valid_transition_destination.

Qed.

Theorem derivable_sequents_vlsm_valid : 
  forall (Γ Δ : list Formula), 
    derivable_sequent(seq Γ Δ) -> 
      vlsm_valid_sequent (seq Γ Δ).

Proof.
  intros Γ.
  intros Δ.

  unfold derivable_sequent.
  intros [k Hderiv].
  induction Hderiv.
  - cut (input_valid_transition sequent_vlsm (existT I_V_ID A)
      (` (composite_s0 sequent_vlsm_components), None)
      (` (composite_s0 sequent_vlsm_components), Some (seq [A] [A]))
    ); [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. by destruct composite_s0.
    + apply option_valid_message_None.
    + by simpl; rewrite state_update_id.
  - cut (input_valid_transition sequent_vlsm (existT I_V_BOT ())
      (` (composite_s0 sequent_vlsm_components), None)
      (` (composite_s0 sequent_vlsm_components), Some (seq [⊥] []))
    );       [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + apply option_valid_message_None.
    + by simpl; rewrite state_update_id.
  - cut (input_valid_transition sequent_vlsm (existT I_V_TOP ())
      (` (composite_s0 sequent_vlsm_components), None)
      (` (composite_s0 sequent_vlsm_components), Some (seq [] [⊤]))
    );       [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + apply option_valid_message_None.
    + by simpl; rewrite state_update_id.
  - cut (input_valid_transition sequent_vlsm (existT I_V_IMP_RIGHT ())
      (` (composite_s0 sequent_vlsm_components), Some (seq (A :: Γ0) (B :: Δ0)))
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 ((A→B) :: Δ0)))
    );          [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + auto.
    + by simpl; rewrite state_update_id. 
  - pose (s0 := ` (composite_s0 sequent_vlsm_components)).
    pose (s1 := state_update sequent_vlsm_components s0 I_V_IMP_LEFT 
                (Some (seq Γ1 (A :: Δ1)))
         ).
    assert (Ht1: input_valid_transition sequent_vlsm (existT I_V_IMP_LEFT recRight) 
                (s0, Some (seq Γ1 (A :: Δ1))) (s1, None)
           ).
    {
      repeat split.
      - by apply initial_state_is_valid; destruct composite_s0.
      - done.
    }
    cut (input_valid_transition sequent_vlsm (existT I_V_IMP_LEFT emitRight)
          (s1, Some (seq (B :: Γ2) Δ2)) (s0, Some (seq ((A → B) :: Γ1 ++ Γ2) (Δ1 ++ Δ2))));
          [by eapply input_valid_transition_out |].
    repeat split.
    + by eapply input_valid_transition_destination.
    + done.
    + cbn. unfold s1. by state_update_simpl. 
    + cbn. unfold s1. rewrite state_update_eq.
      simpl.
      rewrite state_update_twice.
      by rewrite state_update_id.
  - cut (input_valid_transition sequent_vlsm (existT I_V_CONJ_LEFT_1 B)
      (` (composite_s0 sequent_vlsm_components), Some (seq (A :: Γ0)  Δ0))
      (` (composite_s0 sequent_vlsm_components), Some (seq ((A∧B) :: Γ0) Δ0))
    );          [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + auto.
    + by simpl; rewrite state_update_id. 
  - cut (input_valid_transition sequent_vlsm (existT I_V_CONJ_LEFT_2 B)
      (` (composite_s0 sequent_vlsm_components), Some (seq (A :: Γ0)  Δ0))
      (` (composite_s0 sequent_vlsm_components), Some (seq ((B∧A) :: Γ0) Δ0))
    );          [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + auto.
    + by simpl; rewrite state_update_id. 
  - pose (s0 := ` (composite_s0 sequent_vlsm_components)).
    pose (s1 := state_update sequent_vlsm_components s0 I_V_CONJ_RIGHT 
                (Some (seq Γ0 (A :: Δ0)))
          ).
    assert (Ht1: input_valid_transition sequent_vlsm (existT I_V_CONJ_RIGHT rec) 
                (s0, Some (seq Γ0 (A :: Δ0))) (s1, None)
           ).
    {
      repeat split.
      - by apply initial_state_is_valid; destruct composite_s0.
      - done.
    }
    cut (input_valid_transition sequent_vlsm (existT I_V_CONJ_RIGHT emit)
          (s1, Some (seq Γ0 (B :: Δ0))) (s0, Some (seq Γ0 ((A ∧ B) :: Δ0))));
          [by eapply input_valid_transition_out |].
    repeat split.
    + by eapply input_valid_transition_destination.
    + done.
    + by simpl; unfold s1; state_update_simpl.
    + cbn. unfold s1. rewrite state_update_eq.
      rewrite (list_formula_eq_refl).
      rewrite (list_formula_eq_refl).
      simpl.
      rewrite state_update_twice.
      by rewrite state_update_id.
  - pose (s0 := ` (composite_s0 sequent_vlsm_components)).
    pose (s1 := state_update sequent_vlsm_components s0 I_V_DISJ_LEFT 
                (Some (seq (A :: Γ0) Δ0))
         ).
    assert (Ht1: input_valid_transition sequent_vlsm (existT I_V_DISJ_LEFT rec) 
                (s0, Some (seq (A :: Γ0) Δ0)) (s1, None)
           ).
    {
      repeat split.
      - by apply initial_state_is_valid; destruct composite_s0.
      - done.
    }
    cut (input_valid_transition sequent_vlsm (existT I_V_DISJ_LEFT emit)
          (s1, Some (seq (B :: Γ0) Δ0)) (s0, Some (seq ((A ∨ B) :: Γ0) Δ0)));
          [by eapply input_valid_transition_out |].
    repeat split.
    + by eapply input_valid_transition_destination.
    + done.
    + simpl. unfold s1. state_update_simpl. 
      by rewrite list_formula_eq_refl; rewrite list_formula_eq_refl.
    + cbn. unfold s1. rewrite state_update_eq.
      rewrite (list_formula_eq_refl).
      rewrite (list_formula_eq_refl).
      simpl.
      rewrite state_update_twice.
      by rewrite state_update_id.
  - cut (input_valid_transition sequent_vlsm (existT I_V_DISJ_RIGHT_1 B)
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 (A :: Δ0)))
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 ((A∨B) :: Δ0)))
    );          [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + auto.
    + by simpl; rewrite state_update_id. 
  - cut (input_valid_transition sequent_vlsm (existT I_V_DISJ_RIGHT_2 B)
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 (A :: Δ0)))
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 ((B∨A) :: Δ0)))
    );          [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + auto.
    + by simpl; rewrite state_update_id. 
  - cut (input_valid_transition sequent_vlsm (existT I_V_WK_LEFT A)
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 Δ0))
      (` (composite_s0 sequent_vlsm_components), Some (seq (A :: Γ0) Δ0))
    );          [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + auto.
    + by simpl; rewrite state_update_id.
  - cut (input_valid_transition sequent_vlsm (existT I_V_WK_RIGHT A)
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 Δ0))
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 (A :: Δ0)))
    );          [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + auto.
    + by simpl; rewrite state_update_id.
  - cut (input_valid_transition sequent_vlsm (existT I_V_CT_RIGHT ())
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 (A :: A :: Δ0)))
      (` (composite_s0 sequent_vlsm_components), Some (seq Γ0 (A :: Δ0)))
    );          [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + auto.
    + cbn. destruct (decide (A = A)) as [Heq | Hneq].
      * auto.
      * exfalso. by apply Hneq.
    + simpl. destruct (decide (A = A)) as [Heq | Hneq].
      * by rewrite state_update_id.
      * exfalso. by apply Hneq.
  - cut (input_valid_transition sequent_vlsm (existT I_V_CT_LEFT ())
      (` (composite_s0 sequent_vlsm_components), Some (seq (A :: A :: Γ0) Δ0 ))
      (` (composite_s0 sequent_vlsm_components), Some (seq (A :: Γ0) Δ0 ))
    );          [by eapply input_valid_transition_out |].
    repeat split.
    + apply initial_state_is_valid. destruct composite_s0. auto.
    + auto.
    + cbn. destruct (decide (A = A)) as [Heq | Hneq].
      * auto.
      * exfalso. by apply Hneq.
    + simpl. destruct (decide (A = A)) as [Heq | Hneq].
      * by rewrite state_update_id.
      * exfalso. by apply Hneq.
  - by apply xchg_left_vlsm_valid.
  - by apply xchg_right_vlsm_valid.
Qed.

(* Property defined on traces, meaning that all messages, input and output, represent derivable_sequents *)
Definition trace_messages_derivable_sequents (tr : list (transition_item sequent_vlsm)): Prop :=
  forall (m: Sequent), trace_has_message item_sends_or_receives m tr -> derivable_sequent m.

Lemma elem_to_exists {A} (P : A → Prop) (x : A) (l : list A) :
  x ∈ l → P x → Exists P l.
Proof.
  intros H_in H_P.
  apply elem_of_list_In in H_in.
  apply Exists_exists.
  exists x.
  split; assumption.
Qed.


Lemma elem_derivable_input :
  forall (tr : list (transition_item sequent_vlsm)) (e : transition_item) (m : Sequent), 
    e ∈ tr -> trace_messages_derivable_sequents tr
       -> input e = Some m -> derivable_sequent m.
Proof.
  intros tr e m.
  intros Hin Hder Hsome.
  unfold trace_messages_derivable_sequents in Hder.
  specialize (Hder m).
  unfold trace_has_message in Hder.
  apply Hder.
  apply (elem_to_exists (item_sends_or_receives m) e tr Hin).
  unfold item_sends_or_receives.
  by left.  
Qed.

(* Helper lemma to prove that trace_messages_derivable_sequents is preserved over app*)
Lemma trace_messages_derivable_sequents_app : 
  forall (tr_1 tr_2 : list (transition_item sequent_vlsm)), 
      trace_messages_derivable_sequents tr_1 ->
      trace_messages_derivable_sequents tr_2 -> 
        trace_messages_derivable_sequents (tr_1 ++ tr_2).
Proof.
  intros tr1 tr2 Htr1 Htr2.
  intros m Hm.

  apply Exists_app in Hm.
  destruct Hm.
  - exact (Htr1 m H).
  - exact (Htr2 m H).
Qed.
  

Lemma elem_of_list_split {A : Type} (x : A) (l : list A) :
  x ∈ l -> ∃ l1 l2, l = l1 ++ x :: l2.
Proof.
  induction l as [| a l IH]; intros H.
  - rewrite elem_of_nil in H. contradiction.
  - rewrite elem_of_cons in H. destruct H as [-> | H'].
    + exists [], l. reflexivity.
    + destruct (IH H') as [l1 [l2 ->]]. exists (a :: l1), l2. reflexivity.
Qed.


Lemma input_valid_transition_in 
  {message : Type}
  {X : VLSM message}
  (is s : state X)
  (tr : list transition_item)
  (Htrv : finite_valid_trace_init_to X is s tr)
  (itm : transition_item)
  (Hitm : itm ∈ tr) :
    exists (tr_1 tr_2 : list transition_item) (lst_1 := finite_trace_last is tr_1),
      tr = tr_1 ++ [itm] ++ tr_2 /\ input_valid_transition X (l itm) (lst_1, input itm) (destination itm, output itm).
Proof.
  remember (elem_of_list_split itm tr Hitm) as Hspl.
  destruct HeqHspl, Hspl as [l1 [l2 Hspl]].
  rewrite cons_eq_app in Hspl.
  exists l1, l2.
  intros.
  split.
  exact Hspl.
  apply finite_valid_trace_init_to_forget_last in Htrv.
  destruct Htrv as [Htrv _]. 
  exact (input_valid_transition_to X is tr l1 l2 itm Htrv Hspl).
Qed.

Lemma VLSM_comp_eq: VLSM_eq {| vlsm_type := composite_type sequent_vlsm_components; vlsm_machine := free_composite_vlsm_machine sequent_vlsm_components |}
                          (composite_vlsm sequent_vlsm_components (free_constraint sequent_vlsm_components)).
Proof.
  apply free_composite_vlsm_spec.
Qed.

Lemma nil_neq_app_cons : forall (A : Type) (l : list A) (x : A),
  [] <> l ++ [x].
Proof.
  intros A l x H.
  destruct l; simpl in H; discriminate.
Qed.


Lemma length_zero_nil : forall (A : Type) (l : list A),
  length l = 0 -> l = [].
Proof.
  intros A l H.
  destruct l as [| x xs].
  - reflexivity.
  - simpl in H. discriminate H.
Qed.


(* Helper lemma to prove that all valid traces, use as i/o only derivable sequents as messages *)

Lemma all_valid_traces_derivable_sequents : 
  forall {si sf : state sequent_vlsm} {tr : list (transition_item sequent_vlsm)}, 
    finite_valid_trace_init_to sequent_vlsm si sf tr -> trace_messages_derivable_sequents tr.
Proof.
  intros si sf tr Htr.
  (* TODO: Define an easier to use induction principle 
           based on an assertion an all I/Os of a trace.
  *)
  induction Htr using finite_valid_trace_init_to_rev_strong_ind.
  
  intros m Hemp.
  inversion Hemp.

  (* Input should be none or derivable *)
  assert (some_input_derivable: forall (s : Sequent), iom = Some s -> derivable_sequent s). 
  {
    intros s0.
    intros Hsome.
    subst.

    unfold empty_initial_message_or_final_output in Heqiom.
    specialize (IHHtr2 s0).

    destruct (has_last_or_null iom_tr).
    - (* iom is produced in iom_tr*)
      destruct s1 as [l' [a Heq]].
      apply IHHtr2.
      rewrite Heq.
      apply Exists_app.
      right.
      apply Exists_cons_hd.
      right. 
      exact Heqiom.
    - (* iom_tr is empty and iom initial message -> False *)
      destruct Heqiom as [idx [mi Hmi]].
      destruct idx, mi, i.
  }
  unfold trace_messages_derivable_sequents.
  intros m Htrapp.
  apply Exists_app in Htrapp.
  destruct Htrapp.

  (* If the sequent comes from the prefix tr, 
    we already know it's derivable from the induction Hypothesis *)

  (* unfold trace_messages_derivable_sequents in IHHtr1. *)
  exact (IHHtr1 m H).
  
  (* The remaining case is with m in the last transtion as I/O *)

  inversion H; [| by inversion H1].
  subst.
  inversion H1; simpl in H0; subst.

  (* Input of the current transition is m, we already asserted that it is derivable *)
  subst.
  apply (some_input_derivable m).
  reflexivity.

  (* Output, the hard case, where we have to go back through the trace. *)
  (* To reverse the trace we should first check the label and the vlsm emiting m *)
  destruct l as [idx lbl], idx, iom; 
  
  (* Unravel validity predicates *)
  destruct Ht as [[Hv1 [Hv2 Hv3]] Htr]; 

  (* Filter out invalid transitions *)
  try by inversion Hv3.
  - simpl in Htr.
    injection Htr as _ Hlb.
    subst.
    exists 0. apply SC_ID.
  - simpl in Htr. 
    injection Htr as _ Hbot.
    subst.
    exists 0. apply SC_BOT.
  - simpl in Htr.
    injection Htr as _ Htop.
    subst.
    exists 0. apply SC_TOP.
  - simpl in Htr.
    destruct s0 as [L R].
    destruct L as [| A Γ].
    inversion Htr.
    destruct R as [| B Δ];
    inversion Htr.
    subst.
    specialize (some_input_derivable (seq (A :: Γ) (B :: Δ))).
    cut (derivable_sequent (seq (A :: Γ) (B :: Δ)));
      [| by apply some_input_derivable].
    intros [h Hex].
    exists (S h).
    by apply SC_IMP_RIGHT.
  - assert (Hders0: derivable_sequent s0).
    {
      by apply some_input_derivable.
    }
    destruct Hders0 as [hs0].
    simpl in Htr.
    destruct lbl, (s I_V_IMP_LEFT) eqn:Hse; (try by inversion Hse);
    [| | destruct s1 as [[| B Γ'] [| A Δ]] | destruct s1 as [[| B Γ'] [|A Δ]]]; 
      (try by inversion Hse);
    [destruct s0 as [[| B Γ] Δ] | destruct s0 as [Γ [| A Δ]] | destruct s0 as [Γ [| A Δ]] | destruct s0 as [Γ [| A0 Δ']]| destruct s0 as [[| B Γ'] Δ']| destruct s0 as [[| B0 Γ] Δ']]; inversion Htr.
    + cut (derivable_sequent (seq (B :: Γ') [])).
      * intros [hr].
        exists (S (max hs0 hr)).
        exact (SC_IMP_LEFT A B Γ Γ' Δ [] hs0 hr H0 H2).
      * assert (Hprev_s: exists item, 
                        item ∈ tr /\
                        destination item I_V_IMP_LEFT = s I_V_IMP_LEFT /\
                        projT1 (l item) = I_V_IMP_LEFT).
        {
          remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is s tr) as Hqq.
          destruct HeqHqq.

          destruct Hqq as [Hl1 Hr1].

          remember (final_state_component_initial_or_transition I_V_IMP_LEFT is s tr (constraint := free_constraint sequent_vlsm_components) ) as Htt.
          destruct HeqHtt.

          specialize (Htt (Hl1 Htr1)).
          destruct Htt as [Hinit | Htrans].
          - by rewrite Hse in Hinit.
          - destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
            by exists itm.
        }
        destruct Hprev_s as [itm [Hin [Hdest Hproj]]].
        remember (l itm) as tr_lbl eqn: Heq_tr_lbl.
        remember (destination itm) as dest_itm.
        remember (input_valid_transition_in is s tr Htr1 itm Hin) as Htrs. 
        destruct HeqHtrs, Htrs as [tr1 [ tr2 [Htrs Hinp]]].
        remember (finite_trace_last is tr1) as prev_in.
        rewrite <- Heq_tr_lbl in Hinp.
        destruct tr_lbl as [idx lb].
        
        remember (input itm) as inp_itm.
        destruct Heqdest_itm.
        simpl in Hproj.
        destruct Hinp as [Hval Htrans].
        subst idx.
        subst prev_in.
        remember (finite_trace_last is tr1) as s0.
        rewrite Hse in Hdest.
        inversion Htrans as [Htrans'].
        destruct Hval as [Hval1 [_ Hval2]]. simpl in Hval2.
        destruct lb, (s0 I_V_IMP_LEFT); try contradiction; destruct inp_itm; try contradiction;
        destruct s1.
        -- destruct Gamma; try contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
           symmetry in Heqinp_itm.
           remember (elem_derivable_input tr itm (seq (f :: Gamma) Delta) Hin IHHtr1 Heqinp_itm) as Hinp_der.
           by rewrite <- H6, <- H7, <- H8.
        -- destruct Delta. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
        -- destruct Gamma. contradiction.
           destruct s2, Delta0. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
        -- destruct Gamma; contradiction.           
        -- destruct Delta. contradiction.
           destruct s2, Gamma0. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
        -- destruct Delta; contradiction.     
    + cut (derivable_sequent (seq (B :: Γ') (A :: Δ))); remember (A :: Δ) as Δ2.
      * intros [hr].
        exists (S (max hs0 hr)).
        exact (SC_IMP_LEFT A0 B Γ Γ' Δ' Δ2 hs0 hr H0 H2).
      * assert (Hprev_s: exists item, 
                        item ∈ tr /\
                        destination item I_V_IMP_LEFT = s I_V_IMP_LEFT /\
                        projT1 (l item) = I_V_IMP_LEFT).
        {
          remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is s tr) as Hqq.
          destruct HeqHqq.

          destruct Hqq as [Hl1 Hr1].

          remember (final_state_component_initial_or_transition I_V_IMP_LEFT is s tr (constraint := free_constraint sequent_vlsm_components) ) as Htt.
          destruct HeqHtt.

          specialize (Htt (Hl1 Htr1)).
          destruct Htt as [Hinit | Htrans].
          - by rewrite Hse in Hinit.
          - destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
            by exists itm.
        }
        destruct Hprev_s as [itm [Hin [Hdest Hproj]]].
        remember (l itm) as tr_lbl eqn: Heq_tr_lbl.
        remember (destination itm) as dest_itm.
        remember (input_valid_transition_in is s tr Htr1 itm Hin) as Htrs. 
        destruct HeqHtrs, Htrs as [tr1 [ tr2 [Htrs Hinp]]].
        remember (finite_trace_last is tr1) as prev_in.
        rewrite <- Heq_tr_lbl in Hinp.
        destruct tr_lbl as [idx lb].
        
        remember (input itm) as inp_itm.
        destruct Heqdest_itm.
        simpl in Hproj.
        destruct Hinp as [Hval Htrans].
        subst idx.
        subst prev_in.
        remember (finite_trace_last is tr1) as s0.
        rewrite Hse in Hdest.
        inversion Htrans as [Htrans'].
        destruct Hval as [Hval1 [_ Hval2]]. simpl in Hval2.
        destruct lb, (s0 I_V_IMP_LEFT); try contradiction; destruct inp_itm; try contradiction; 
        destruct s1.
        -- destruct Gamma. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
           symmetry in Heqinp_itm.
           remember (elem_derivable_input tr itm (seq (f :: Gamma) Delta) Hin IHHtr1 Heqinp_itm) as Hinp_der.
           by rewrite <- H6, <- H7, <- H8.        
        -- destruct Delta. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
           symmetry in Heqinp_itm.
           subst Gamma.
           exact (elem_derivable_input tr itm (seq (B :: Γ') (f :: Delta)) Hin IHHtr1 Heqinp_itm).
        -- destruct Gamma. contradiction.
           destruct s2, Delta0. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
        -- destruct Gamma; contradiction.
        -- destruct Delta. contradiction.
           destruct s2, Gamma0. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.  
        -- destruct Delta; contradiction.
    + cut (derivable_sequent (seq [] (A :: Δ))).
      * intros [hl].
        exists (S (max hl hs0)).
        exact (SC_IMP_LEFT A B [] Γ' Δ Δ' hl hs0 H2 H0).
      * assert (Hprev_s: exists item, 
                        item ∈ tr /\
                        destination item I_V_IMP_LEFT = s I_V_IMP_LEFT /\
                        projT1 (l item) = I_V_IMP_LEFT).
        {
          remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is s tr) as Hqq.
          destruct HeqHqq.

          destruct Hqq as [Hl1 Hr1].

          remember (final_state_component_initial_or_transition I_V_IMP_LEFT is s tr (constraint := free_constraint sequent_vlsm_components) ) as Htt.
          destruct HeqHtt.

          specialize (Htt (Hl1 Htr1)).
          destruct Htt as [Hinit | Htrans].
          - by rewrite Hse in Hinit.
          - destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
            by exists itm.
        }
        destruct Hprev_s as [itm [Hin [Hdest Hproj]]].
        remember (l itm) as tr_lbl eqn: Heq_tr_lbl.
        remember (destination itm) as dest_itm.
        remember (input_valid_transition_in is s tr Htr1 itm Hin) as Htrs. 
        destruct HeqHtrs, Htrs as [tr1 [ tr2 [Htrs Hinp]]].
        remember (finite_trace_last is tr1) as prev_in.
        rewrite <- Heq_tr_lbl in Hinp.
        destruct tr_lbl as [idx lb].
        
        remember (input itm) as inp_itm.
        destruct Heqdest_itm.
        simpl in Hproj.
        destruct Hinp as [Hval Htrans].
        subst idx.
        subst prev_in.
        remember (finite_trace_last is tr1) as s0.
        rewrite Hse in Hdest.
        inversion Htrans as [Htrans'].
        destruct Hval as [Hval1 [_ Hval2]]. simpl in Hval2.
        destruct lb, (s0 I_V_IMP_LEFT); try contradiction; destruct inp_itm; try contradiction; 
        destruct s1.
        -- destruct Gamma. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
        -- destruct Delta. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
           symmetry in Heqinp_itm.
           subst Gamma.
           subst f.
           subst Delta.
           exact (elem_derivable_input tr itm (seq [] (A :: Δ)) Hin IHHtr1 Heqinp_itm).
        -- destruct Gamma. contradiction.
           destruct s2, Delta0. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
        -- destruct Gamma; contradiction.
        -- destruct Delta. contradiction.
           destruct s2, Gamma0. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
        -- destruct Delta; contradiction.
    + cut (derivable_sequent(seq (B :: Γ') (A :: Δ))).
      * intros [hl].
        exists (S (max hl hs0)).
        exact (SC_IMP_LEFT A B0 (B :: Γ') Γ Δ Δ' hl hs0 H2 H0).
      * assert (Hprev_s: exists item, 
                        item ∈ tr /\
                        destination item I_V_IMP_LEFT = s I_V_IMP_LEFT /\
                        projT1 (l item) = I_V_IMP_LEFT).
        {
          remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is s tr) as Hqq.
          destruct HeqHqq.

          destruct Hqq as [Hl1 Hr1].

          remember (final_state_component_initial_or_transition I_V_IMP_LEFT is s tr (constraint := free_constraint sequent_vlsm_components) ) as Htt.
          destruct HeqHtt.

          specialize (Htt (Hl1 Htr1)).
          destruct Htt as [Hinit | Htrans].
          - by rewrite Hse in Hinit.
          - destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
            by exists itm.
        }
        destruct Hprev_s as [itm [Hin [Hdest Hproj]]].
        remember (l itm) as tr_lbl eqn: Heq_tr_lbl.
        remember (destination itm) as dest_itm.
        remember (input_valid_transition_in is s tr Htr1 itm Hin) as Htrs. 
        destruct HeqHtrs, Htrs as [tr1 [ tr2 [Htrs Hinp]]].
        remember (finite_trace_last is tr1) as prev_in.
        rewrite <- Heq_tr_lbl in Hinp.
        destruct tr_lbl as [idx lb].
        
        remember (input itm) as inp_itm.
        destruct Heqdest_itm.
        simpl in Hproj.
        destruct Hinp as [Hval Htrans].
        subst idx.
        subst prev_in.
        remember (finite_trace_last is tr1) as s0.
        rewrite Hse in Hdest.
        inversion Htrans as [Htrans'].
        destruct Hval as [Hval1 [_ Hval2]]. simpl in Hval2.
        destruct lb, (s0 I_V_IMP_LEFT); try contradiction; destruct inp_itm; try contradiction; 
        destruct s1.
        -- destruct Gamma. contradiction.
          inversion Htrans' as [Hsdest].
          pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
          simpl in Himps.
          rewrite state_update_eq in Himps.
          rewrite Hdest in Himps.
          inversion Himps.
          subst f. subst Gamma. subst Delta.
          symmetry in Heqinp_itm.
          exact (elem_derivable_input tr itm (seq (B :: Γ') (A :: Δ)) Hin IHHtr1 Heqinp_itm).
        -- destruct Delta. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
           subst f. subst Gamma. subst Delta.
           symmetry in Heqinp_itm.
           exact (elem_derivable_input tr itm (seq (B :: Γ') (A :: Δ)) Hin IHHtr1 Heqinp_itm).
        -- destruct Gamma. contradiction.
           destruct s2, Delta0. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
        -- destruct Gamma; contradiction.
        -- destruct Delta. contradiction.
           destruct s2, Gamma0. contradiction.
           inversion Htrans' as [Hsdest].
           pose proof (f_equal (fun h => h I_V_IMP_LEFT) Hsdest) as Himps.
           simpl in Himps.
           rewrite state_update_eq in Himps.
           rewrite Hdest in Himps.
           inversion Himps.
        -- destruct Delta; contradiction.
  - simpl in Hv3.
    destruct lbl, (s I_V_IMP_LEFT); try contradiction; 
    destruct s0; 
      [by destruct Gamma | by destruct Delta].
  - simpl in Htr.
    destruct s0 as [L Δ].
    destruct L as [| A Γ];
    inversion Htr.
    subst.
    specialize (some_input_derivable (seq (A :: Γ) Δ)).
    cut (derivable_sequent (seq (A :: Γ) Δ));
      [| by apply some_input_derivable].
    intros [h Hex].
    exists (S h).
    apply SC_CONJ_LEFT_1.
    exact Hex.

  - simpl in Htr.
    destruct s0 as [L Δ].
    destruct L as [| A Γ];
    inversion Htr.
    subst.
    specialize (some_input_derivable (seq (A :: Γ) Δ)).
    cut (derivable_sequent (seq (A :: Γ) Δ));
      [| by apply some_input_derivable].
    intros [h Hex].
    exists (S h).
    apply SC_CONJ_LEFT_2.
    exact Hex.

  - simpl in Htr.
    destruct lbl, (s I_V_CONJ_RIGHT) eqn:Hse;
     [by inversion Htr | | | by inversion Htr]. 
    destruct s0, Delta; [by inversion Htr | by inversion Htr].

    destruct s1 as [Γ [| A Δ]]. by inversion Htr.
    destruct s0 as [Γ' [| B Δ']]. by inversion Htr.
    unfold list_formula_eq in Htr.
    destruct (decide (Γ = Γ')), (decide (Δ = Δ')); 
    inversion Htr.
    specialize (some_input_derivable (seq Γ' (B :: Δ'))).
    symmetry in e, e0, H2, H3.
    subst.
    assert (Hdr: derivable_sequent (seq Γ (B :: Δ))). 
    {
      by apply some_input_derivable.
    }
    inversion Hdr as [hr].
    cut (derivable_sequent (seq Γ (A :: Δ))).
    + intros Hdl.
      inversion Hdl as [hl].
      exists (S (max hl hr)).
      apply (SC_CONJ_RIGHT A B Γ Δ hl hr H2 H0).

    + assert (Hprev_s: exists item, 
                        item ∈ tr /\
                        destination item I_V_CONJ_RIGHT = s I_V_CONJ_RIGHT /\
                        projT1 (l item) = I_V_CONJ_RIGHT).
      {
        remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is s tr) as Hqq.
        destruct HeqHqq.

        destruct Hqq as [Hl1 Hr1].
        remember (final_state_component_initial_or_transition I_V_CONJ_RIGHT is s tr (constraint := free_constraint sequent_vlsm_components) ) as Htt.
        destruct HeqHtt.
        specialize (Htt (Hl1 Htr1)).
        destruct Htt as [Hinit | Htrans].
        - by rewrite Hse in Hinit.
        - destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
          by exists itm.
      }
      destruct Hprev_s as [itm [Hin [Hdest Hproj]]].
      remember (l itm) as tr_lbl eqn: Heq_tr_lbl.
      remember (destination itm) as dest_itm.
      remember (input_valid_transition_in is s tr Htr1 itm Hin) as Htrs. 
      destruct HeqHtrs, Htrs as [tr1 [ tr2 [Htrs Hinp]]].
      remember (finite_trace_last is tr1) as prev_in.
      rewrite <- Heq_tr_lbl in Hinp.
      destruct tr_lbl as [idx lb].
      
      remember (input itm) as inp_itm.
      destruct Heqdest_itm.
      simpl in Hproj.
      destruct Hinp as [Hval Htrans].
      subst idx.
      subst prev_in.
      remember (finite_trace_last is tr1) as s0.
      rewrite Hse in Hdest.
      inversion Htrans as [Htrans'].
      destruct Hval as [Hval1 [_ Hval2]]. simpl in Hval2.
      destruct lb eqn:Heq_lb, (s0 I_V_CONJ_RIGHT); [contradiction | | | contradiction]; 
        [| destruct s1, Delta]; try contradiction.
      * destruct inp_itm; [| contradiction].
        destruct s1.
        destruct Delta. contradiction.
        inversion Htrans' as [Hstrans].
        pose proof (f_equal (fun h => h I_V_CONJ_RIGHT) Hstrans) as Hsconj.
        simpl in Hsconj.
        rewrite state_update_eq in Hsconj.
        rewrite Hdest in Hsconj.
        inversion Hsconj as [Hseq].
        symmetry in Heqinp_itm.
        remember (elem_derivable_input tr itm (seq Gamma (f :: Delta)) Hin IHHtr1 Heqinp_itm) as Hinp_der.
        by rewrite <- Hseq, <- H3, <- H4.

      * destruct inp_itm; [| contradiction].
        destruct s1.
        destruct Delta0. contradiction.
        unfold list_formula_eq in Htrans'.
        destruct (decide (Gamma = Gamma0)), (decide (Delta = Delta0)); simpl in Htrans'; inversion Htrans' as [Hstrans];
        pose proof (f_equal (fun h => h I_V_CONJ_RIGHT) Hstrans) as Hsconj; simpl in Hsconj; rewrite state_update_eq in Hsconj;
        rewrite Hdest in Hsconj; by inversion Hsconj.

  - simpl in Hv3.
    destruct lbl, (s I_V_CONJ_RIGHT); try contradiction.
    destruct s0; by destruct Delta.
  - simpl in Htr.
    destruct lbl, (s I_V_DISJ_LEFT) eqn:Hse;
    [by inversion Htr | | destruct s1 as [[| A Γ] Δ]| by inversion Htr]; 
    destruct s0 as [[| B Γ'] Δ']; 
    try by inversion Htr.
    unfold list_formula_eq in Htr.
    destruct (decide (Γ = Γ')), (decide (Δ = Δ'));
    simpl in Htr; inversion Htr.
    specialize (some_input_derivable (seq (B :: Γ') Δ')).
    symmetry in e, e0, H2, H3.
    subst.

    assert (Hdr: derivable_sequent (seq (B :: Γ) Δ)).
    {
      by apply some_input_derivable.
    }

    inversion Hdr as [hr].
    cut (derivable_sequent(seq (A :: Γ) Δ)).
    + intros [hl].
      exists (S (max hl hr)).
      apply (SC_DISJ_LEFT A B Γ Δ hl hr H2 H0).
    + assert (Hprev_s: exists item, 
                        item ∈ tr /\
                        destination item I_V_DISJ_LEFT = s I_V_DISJ_LEFT /\
                        projT1 (l item) = I_V_DISJ_LEFT).
      {
        remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is s tr) as Hqq.
        destruct HeqHqq.

        destruct Hqq as [Hl1 Hr1].
        remember (final_state_component_initial_or_transition I_V_DISJ_LEFT is s tr (constraint := free_constraint sequent_vlsm_components) ) as Htt.
        destruct HeqHtt.
        specialize (Htt (Hl1 Htr1)).
        destruct Htt as [Hinit | Htrans].
        - by rewrite Hse in Hinit.
        - destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
          by exists itm.
      }

      destruct Hprev_s as [itm [Hin [Hdest Hproj]]].
      remember (l itm) as tr_lbl eqn: Heq_tr_lbl.
      remember (destination itm) as dest_itm.
      remember (input_valid_transition_in is s tr Htr1 itm Hin) as Htrs. 
      destruct HeqHtrs, Htrs as [tr1 [ tr2 [Htrs Hinp]]].
      remember (finite_trace_last is tr1) as prev_in.
      rewrite <- Heq_tr_lbl in Hinp.
      destruct tr_lbl as [idx lb].
      
      remember (input itm) as inp_itm.
      destruct Heqdest_itm.
      simpl in Hproj.
      destruct Hinp as [Hval Htrans].
      subst idx.
      subst prev_in.
      remember (finite_trace_last is tr1) as s0.
      rewrite Hse in Hdest.
      inversion Htrans as [Htrans'].
      destruct Hval as [Hval1 [_ Hval2]]. simpl in Hval2.
      destruct lb, (s0 I_V_DISJ_LEFT); [contradiction | | destruct s1, Gamma | contradiction]; 
      [ | contradiction | ]; destruct inp_itm; [| contradiction | | contradiction]; destruct s1; [destruct Gamma | destruct Gamma0];
      try contradiction; [| (unfold list_formula_eq in *; destruct (decide (Gamma = Gamma0)), (decide (Delta = Delta0)))]; 
      simpl in *; try contradiction; inversion Htrans'; inversion Htrans' as [Hstrans];
      pose proof (f_equal (fun h => h I_V_DISJ_LEFT) Hstrans) as Hsdisj; simpl in Hsdisj; rewrite state_update_eq in Hsdisj;
      rewrite Hdest in Hsdisj; inversion Hsdisj as [Hseq]. 
      symmetry in Heqinp_itm.
      remember (elem_derivable_input tr itm (seq (f :: Gamma) Delta) Hin IHHtr1 Heqinp_itm) as Hinp_der.
      by rewrite <- Hseq, <- H5, <- H6.

  - simpl in Hv3.
    destruct lbl, (s I_V_DISJ_LEFT); try contradiction.
    by destruct s0, Gamma.
  - simpl in Htr.
    destruct s0 as [Γ [| A Δ]];
    inversion Htr.
    subst.
    specialize (some_input_derivable (seq Γ (A :: Δ))).
    cut (derivable_sequent (seq Γ (A :: Δ)));
      [| by apply some_input_derivable].
    intros [h Hex].
    exists (S h).
    apply SC_DISJ_RIGHT_1.
    exact Hex.
  - simpl in Htr.
    destruct s0 as [Γ [| A Δ]];
    inversion Htr.
    subst.
    specialize (some_input_derivable (seq Γ (A :: Δ))).
    cut (derivable_sequent (seq Γ (A :: Δ)));
      [| by apply some_input_derivable].
    intros [h Hex].
    exists (S h).
    apply SC_DISJ_RIGHT_2.
    exact Hex.
  - simpl in Htr.
    destruct s0 as [Γ Δ].
    inversion Htr.
    subst.
    specialize (some_input_derivable (seq Γ Δ)).
    cut (derivable_sequent (seq Γ Δ));
      [| by apply some_input_derivable].
    intros [h Hex].
    exists (S h).
    apply SC_WK_LEFT.
    exact Hex.
  - simpl in Htr.
    destruct s0 as [Γ Δ].
    inversion Htr.
    subst.
    specialize (some_input_derivable (seq Γ Δ)).
    cut (derivable_sequent (seq Γ Δ));
      [| by apply some_input_derivable].
    intros [h Hex].
    exists (S h).
    apply SC_WK_RIGHT.
    exact Hex.
  - simpl in Htr.
    destruct s0 as [[| A [| B Γ]] Δ];
    inversion Htr.
    destruct (decide (A = B));
    inversion H2.
    subst.
    specialize (some_input_derivable (seq (B :: B :: Γ) Δ)).
    cut (derivable_sequent (seq (B :: B :: Γ) Δ));
        [| by apply some_input_derivable].
    intros [h Hex].
    exists (S h).
    apply SC_CT_LEFT.
    exact Hex.
  - simpl in Htr.
    destruct s0 as [Γ [| A [| B Δ]]];
    inversion Htr.
    destruct (decide (A = B));
    inversion H2.
    subst.
    specialize (some_input_derivable (seq Γ (B :: B :: Δ))).
    cut (derivable_sequent (seq Γ (B :: B :: Δ)));
        [| by apply some_input_derivable].
    intros [h Hex].
    exists (S h).
    apply SC_CT_RIGHT.
    exact Hex.
  - simpl in Htr.
    destruct lbl, (s I_V_XCHG_LEFT), o;
    [destruct l | destruct l | destruct s1 | by inversion Htr | destruct s1 | by inversion Htr ]; (try by inversion Htr).
    destruct s0. inversion Htr.
    destruct Gamma; inversion Htr.
    destruct Gamma. inversion Htr.
    destruct Gamma. inversion Htr.
    inversion Htr.
  - simpl in Htr.
    destruct lbl, (s I_V_XCHG_LEFT) eqn:Hse; [destruct l| | ]; (try by inversion Htr); 
    destruct o; (try by inversion Htr); destruct s0; destruct Gamma; [| | | destruct Gamma]; try by inversion Htr.
    inversion Htr.
    rename l into Σ, f0 into C, f into B, Gamma into Γ, Delta into Δ.
    assert (Hprev_s: forall is s tr Σ Γ Δ, 
            finite_valid_trace_init_to sequent_vlsm is s tr -> s I_V_XCHG_LEFT = (Σ, Some (seq Γ Δ))
            -> exists item, item ∈ tr /\
                            destination item I_V_XCHG_LEFT = s I_V_XCHG_LEFT /\
                            projT1 (l item) = I_V_XCHG_LEFT).
    {
      intros is0 s0 tr0 Σ0 Γ0 Δ0.
      intros Htr0.
      intros Hs0e.

      remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is0 s0 tr0) as Hqq.
      destruct HeqHqq.

      destruct Hqq as [Hl1 Hr1].
      remember (final_state_component_initial_or_transition I_V_XCHG_LEFT is0 s0 tr0 (constraint := free_constraint sequent_vlsm_components) ) as Htt.
      destruct HeqHtt.
      specialize (Htt (Hl1 Htr0)).
      destruct Htt as [Hinit | Htrans].
      - by rewrite Hs0e in Hinit.
      - destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
        by exists itm.
    }
    assert (H_prev_inv: forall is s tr Σ A Γ Δ,
             finite_valid_trace_init_to sequent_vlsm is s tr -> s I_V_XCHG_LEFT = (Σ ++ [A], Some (seq Γ Δ))
              -> exists item, item ∈ tr /\
                            destination item I_V_XCHG_LEFT = (Σ, Some (seq (A :: Γ) Δ)) /\
                            projT1 (l item) = I_V_XCHG_LEFT).
    {
      intros is0 s0 tr0 Σ0 A0 Γ0 Δ0.
      intros Htr0.
      intros Hs0e.
      remember (Hprev_s is0 s0 tr0 (Σ0 ++ [A0]) Γ0 Δ0 Htr0 Hs0e) as Hprev.
      destruct HeqHprev.
      
      destruct Hprev as [itm [Hin [Hdest Hproj]]].
      remember (l itm) as tr_lbl eqn: Heq_tr_lbl.
      remember (input_valid_transition_in is0 s0 tr0 Htr0 itm Hin) as Htrs. 
      destruct HeqHtrs, Htrs as [tr1 [ tr2 [Htrs Hinp]]].
      remember (finite_trace_last is tr1) as prev_in.
      rewrite <- Heq_tr_lbl in Hinp.
      destruct tr_lbl as [idx lb].

      remember (input itm) as inp_itm.
      simpl in Hproj.
      destruct Hinp as [Hval Htrans].
      remember (destination itm) as dest_itm.
      subst idx.
      subst prev_in.
      remember (finite_trace_last is0 tr1) as s'.
      pose proof Htr0 as Htr0'.
      rewrite Htrs in Htr0'.
      rewrite app_assoc in Htr0'.
      pose proof (finite_valid_trace_init_to_prefix_1 sequent_vlsm Htr0') as Hpref.
      unfold finite_trace_last in Hpref.
      assert (Hlast: last (map destination (tr1 ++ [itm])) is0 = dest_itm).
      {
        rewrite map_app.
        simpl.
        by rewrite last_app.
      }
      rewrite Hlast in Hpref.
      simpl in Htrans.
      destruct Hval as [_ [_ Hval]].
      simpl in Hval.

      destruct lb, (s' I_V_XCHG_LEFT) eqn:Hs'e; [destruct l, o | destruct o | destruct o];
      (try contradiction);
      destruct inp_itm as [[Γ' Δ'] | ]; (try contradiction);
      (try destruct s1);
      (try destruct Gamma);
      (try destruct Gamma);
      (try contradiction);
      injection Htrans as Htrans;
      pose proof (f_equal (fun h => h I_V_XCHG_LEFT) Htrans) as Hloc;
      simpl in Hloc;
      rewrite state_update_eq in Hloc;
      rewrite Hdest in Hloc;
      rewrite Hs0e in Hloc;
      inversion Hloc;
      [by apply nil_neq_app_cons in H5 | |];
    
      apply app_inj_tail in H5; 
      destruct H5 as [HlΣ HfA0];
      subst l; subst f;
      subst Delta; subst Γ0;
      pose (finite_valid_trace_init_to_snoc sequent_vlsm is0 dest_itm tr1 itm) as Hvtr1;
      apply proj1 in Hvtr1;
      specialize (Hvtr1 Hpref);
      rewrite <- Heqs' in Hvtr1;
      destruct Hvtr1 as [Hvtr1 [Hvtr1' _]];
        [pose proof (Hprev_s is0 s' tr1 Σ0 [A0] Δ0 Hvtr1 Hs'e) as Hitm_inv | pose proof (Hprev_s is0 s' tr1 Σ0 (A0 :: (f0 :: Gamma)) Δ0 Hvtr1 Hs'e) as Hitm_inv];
      destruct Hitm_inv as [i [Hitr1 [Hidest Hiproj]]];
      exists i; 
        ((repeat split); [rewrite Htrs; apply elem_of_app; by left | by rewrite Hidest | exact Hiproj]).
    }
    assert (H_prev_capt: forall Σ is s tr  Γ Δ, 
            finite_valid_trace_init_to sequent_vlsm is s tr -> s I_V_XCHG_LEFT = (Σ, Some (seq Γ Δ))
            -> exists item, item ∈ tr /\
                            destination item I_V_XCHG_LEFT = ([], Some (seq (Σ ++ Γ) Δ)) /\
                            projT1 (l item) = I_V_XCHG_LEFT).
    {
      intros Σ0.
      remember (length Σ0) as len_Σ0.
      revert Σ0 Heqlen_Σ0.
      induction len_Σ0.
      - intros Σ0 Hlen is0 s0 tr0 Γ0 Δ0 Htr0 Hs0.
        symmetry in Hlen.
        apply length_zero_nil in Hlen.
        subst Σ0. simpl.
        remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is0 s0 tr0) as Hqq.
        destruct HeqHqq.

        destruct Hqq as [Hl1 Hr1].

        remember (final_state_component_initial_or_transition I_V_XCHG_LEFT is0 s0 tr0 (constraint := free_constraint sequent_vlsm_components) ) as Htt.
        destruct HeqHtt.

        specialize (Htt (Hl1 Htr0)).
        destruct Htt as [Hinit | Htrans].
        + by rewrite Hs0 in Hinit.
        + destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
          exists itm. repeat split.
          * auto.
          * by rewrite Htrans2.
          * auto.
      - intros Σ0 Hlen is0 s0 tr0 Γ0 Δ0 HtrΣ Hs0.
        assert (Hnotnil: Σ0 <> []).
        {
          destruct Σ0 as [|x xs].
          - simpl in Hlen. discriminate Hlen.
          - discriminate.
        }
        pose (exists_last Hnotnil) as Hstp.
        destruct Hstp as [Π [A Heq]].
        
        subst Σ0.
        specialize (H_prev_inv is0 s0 tr0 Π A Γ0 Δ0 HtrΣ Hs0).
        destruct H_prev_inv as [itm [Hin [Hdst Hproj]]].
        rewrite app_length in Hlen.
        simpl in Hlen.
        rewrite Nat.add_1_r in Hlen.
        apply Nat.succ_inj in Hlen.
        pose proof (input_valid_transition_in is0 s0 tr0 HtrΣ itm Hin) as Htrs. 

        destruct Htrs as [tr1 [tr2 [Htrs Hinp]]].
        pose proof HtrΣ as Htrp.
        rewrite Htrs in Htrp.
        rewrite app_assoc in Htrp.
        pose proof (finite_valid_trace_init_to_prefix_1 sequent_vlsm Htrp) as Hpref.
        unfold finite_trace_last in Hpref.
        assert (Hlast: last (map destination (tr1 ++ [itm])) is0 = destination itm).
        {
          rewrite map_app.
          simpl.
          by rewrite last_app.
        }
        rewrite Hlast in Hpref.
        specialize (IHlen_Σ0 Π Hlen is0 (destination itm) (tr1 ++ [itm]) (A :: Γ0) Δ0 Hpref).

        specialize (IHlen_Σ0 Hdst).
        destruct IHlen_Σ0 as [itm_res [Hin_res [Hdst_res Hproj_res]]].
        exists itm_res. repeat split.
        + rewrite Htrs. 
          rewrite app_assoc.
          apply elem_of_app.
          by left.
        + rewrite <- app_assoc.
          by exact Hdst_res.
        + exact Hproj_res.
    }
    cut (derivable_sequent (seq (Σ ++ B :: C :: Γ) Δ)).
    + intros [k H_rec].
      unfold derivable_sequent.
      exists (S k).
      exact (SC_XCHG_LEFT B C Σ Δ Γ k H_rec).
    + specialize (H_prev_capt Σ is s tr (B :: C :: Γ) Δ Htr1 Hse).
      destruct H_prev_capt as [i_capt [Hin_capt [Hdest_capt Hproj_capt]]].
      pose proof (input_valid_transition_in is s tr Htr1 i_capt Hin_capt) as Htrs. 
      destruct Htrs as [tr1 [tr2 [Htrs Hinp]]].

      remember (destination i_capt) as dest_capt.
      remember (input i_capt) as inp_capt.
      remember (l i_capt) as l_capt.
      destruct Hinp as [Hval Htrans].
      destruct l_capt as [idx lb].
      simpl in Hproj_capt.
      subst idx.
      remember (finite_trace_last is tr1) as prev_in.

      simpl in Htrans.
      simpl in Hval.
      destruct Hval as [_ [_ Hval3]].
      destruct lb, (prev_in I_V_XCHG_LEFT) eqn:in_eq; 
      destruct o, l; 
      (try contradiction);
      destruct inp_capt as [[Γ' Δ'] | ]; (try contradiction);
      (try destruct s0);
      (try destruct Gamma);
      (try destruct Gamma);
      (try contradiction);
      injection Htrans as Htrans;
      pose proof (f_equal (fun h => h I_V_XCHG_LEFT) Htrans) as Hloc;
      simpl in Hloc;
      rewrite state_update_eq in Hloc;
      rewrite Hdest_capt in Hloc;
      inversion Hloc.
      
      subst Γ'.
      subst Δ'.
      symmetry in Heqinp_capt.
      exact (elem_derivable_input tr i_capt (seq (Σ ++ B :: C :: Γ) Δ) Hin_capt IHHtr1 Heqinp_capt).

  - simpl in Htr.
    destruct lbl, (s I_V_XCHG_RIGHT); [destruct l, o | destruct o | destruct o];
    destruct s0; (try by inversion Htr); destruct s1, Delta0; (try by inversion Htr).
    destruct Delta0; by inversion Htr.
  - simpl in Htr.
    destruct lbl, (s I_V_XCHG_RIGHT) eqn:Hse; [destruct l, o| destruct o| destruct o]; (try by inversion Htr); 
    destruct s0; destruct Delta; [| | | destruct Delta]; inversion Htr.
    rename l into Σ, f0 into C, f into B, Gamma into Γ, Delta into Δ.
    assert (Hprev_s: forall is s tr Σ Γ Δ, 
            finite_valid_trace_init_to sequent_vlsm is s tr -> s I_V_XCHG_RIGHT = (Σ, Some (seq Γ Δ))
            -> exists item, item ∈ tr /\
                            destination item I_V_XCHG_RIGHT = s I_V_XCHG_RIGHT /\
                            projT1 (l item) = I_V_XCHG_RIGHT).
    {
      intros is0 s0 tr0 Σ0 Γ0 Δ0.
      intros Htr0.
      intros Hs0e.

      remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is0 s0 tr0) as Hqq.
      destruct HeqHqq.

      destruct Hqq as [Hl1 Hr1].
      remember (final_state_component_initial_or_transition I_V_XCHG_RIGHT is0 s0 tr0 (constraint := free_constraint sequent_vlsm_components) ) as Htt.
      destruct HeqHtt.
      specialize (Htt (Hl1 Htr0)).
      destruct Htt as [Hinit | Htrans].
      - by rewrite Hs0e in Hinit.
      - destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
        by exists itm.
    }
    assert (H_prev_inv: forall is s tr Σ A Γ Δ,
             finite_valid_trace_init_to sequent_vlsm is s tr -> s I_V_XCHG_RIGHT = (Σ ++ [A], Some (seq Γ Δ))
              -> exists item, item ∈ tr /\
                            destination item I_V_XCHG_RIGHT = (Σ, Some (seq Γ (A :: Δ))) /\
                            projT1 (l item) = I_V_XCHG_RIGHT).
    {
      intros is0 s0 tr0 Σ0 A0 Γ0 Δ0.
      intros Htr0.
      intros Hs0e.
      remember (Hprev_s is0 s0 tr0 (Σ0 ++ [A0]) Γ0 Δ0 Htr0 Hs0e) as Hprev.
      destruct HeqHprev.
      
      destruct Hprev as [itm [Hin [Hdest Hproj]]].
      remember (l itm) as tr_lbl eqn: Heq_tr_lbl.
      remember (input_valid_transition_in is0 s0 tr0 Htr0 itm Hin) as Htrs. 
      destruct HeqHtrs, Htrs as [tr1 [ tr2 [Htrs Hinp]]].
      remember (finite_trace_last is tr1) as prev_in.
      rewrite <- Heq_tr_lbl in Hinp.
      destruct tr_lbl as [idx lb].

      remember (input itm) as inp_itm.
      simpl in Hproj.
      destruct Hinp as [Hval Htrans].
      remember (destination itm) as dest_itm.
      subst idx.
      subst prev_in.
      remember (finite_trace_last is0 tr1) as s'.
      pose proof Htr0 as Htr0'.
      rewrite Htrs in Htr0'.
      rewrite app_assoc in Htr0'.
      pose proof (finite_valid_trace_init_to_prefix_1 sequent_vlsm Htr0') as Hpref.
      unfold finite_trace_last in Hpref.
      assert (Hlast: last (map destination (tr1 ++ [itm])) is0 = dest_itm).
      {
        rewrite map_app.
        simpl.
        by rewrite last_app.
      }
      rewrite Hlast in Hpref.
      simpl in Htrans.
      destruct Hval as [_ [_ Hval]].   
      simpl in Hval.   
      destruct lb, (s' I_V_XCHG_RIGHT) eqn:Hs'e; [destruct l, o| destruct o| destruct o]; (try contradiction);
      destruct inp_itm; (try contradiction); destruct s1;
      (destruct Delta); (try contradiction); (try destruct Delta); (try contradiction);
      inversion Htrans;
      pose proof (f_equal (fun h => h I_V_XCHG_RIGHT) H4) as Hloc;
      simpl in Hloc;
      rewrite state_update_eq in Hloc;
      rewrite Hdest in Hloc;
      rewrite Hs0e in Hloc;
      inversion Hloc; (try by apply nil_neq_app_cons in H6);
      apply app_inj_tail in H6;
      destruct H6 as [HlΣ HfA0];
      subst l; subst f; subst Gamma; subst Δ0;
      pose (finite_valid_trace_init_to_snoc sequent_vlsm is0 dest_itm tr1 itm) as Hvtr1;
      apply proj1 in Hvtr1;
      specialize (Hvtr1 Hpref);
      destruct Hvtr1 as [Hvtr1 [Hvtr1' _]];
      rewrite <- Heqs' in Hvtr1; 
        [pose proof (Hprev_s is0 s' tr1 Σ0 Γ0 [A0] Hvtr1 Hs'e) as Hitm_inv | pose proof (Hprev_s is0 s' tr1 Σ0 Γ0 (A0 :: (f0 :: Delta)) Hvtr1 Hs'e) as Hitm_inv];
      destruct Hitm_inv as [i [Hitr1 [Hidest Hiproj]]];
      exists i; 
        ((repeat split); [rewrite Htrs; apply elem_of_app; by left | by rewrite Hidest | exact Hiproj]).
    }
    assert (H_prev_capt: forall Σ is s tr  Γ Δ, 
          finite_valid_trace_init_to sequent_vlsm is s tr -> s I_V_XCHG_RIGHT = (Σ, Some (seq Γ Δ))
          -> exists item, item ∈ tr /\
                          destination item I_V_XCHG_RIGHT = ([], Some (seq Γ (Σ ++ Δ))) /\
                          projT1 (l item) = I_V_XCHG_RIGHT).
    {
      intros Σ0.
      remember (length Σ0) as len_Σ0.
      revert Σ0 Heqlen_Σ0.
      induction len_Σ0.
      - intros Σ0 Hlen is0 s0 tr0 Γ0 Δ0 Htr0 Hs0.
        symmetry in Hlen.
        apply length_zero_nil in Hlen.
        subst Σ0. simpl.
        remember (VLSM_eq_finite_valid_trace_init_to VLSM_comp_eq is0 s0 tr0) as Hqq.
        destruct HeqHqq.

        destruct Hqq as [Hl1 Hr1].

        remember (final_state_component_initial_or_transition I_V_XCHG_RIGHT is0 s0 tr0 (constraint := free_constraint sequent_vlsm_components) ) as Htt.
        destruct HeqHtt.

        specialize (Htt (Hl1 Htr0)).
        destruct Htt as [Hinit | Htrans].
        + by rewrite Hs0 in Hinit.
        + destruct Htrans as [itm [Htrans1 [Htrans2 Htrans3]]].
          exists itm. repeat split.
          * auto.
          * by rewrite Htrans2.
          * auto.
      - intros Σ0 Hlen is0 s0 tr0 Γ0 Δ0 HtrΣ Hs0.
        assert (Hnotnil: Σ0 <> []).
        {
          destruct Σ0 as [|x xs].
          - simpl in Hlen. discriminate Hlen.
          - discriminate.
        }
        pose (exists_last Hnotnil) as Hstp.
        destruct Hstp as [Π [A Heq]].
        
        subst Σ0.
        specialize (H_prev_inv is0 s0 tr0 Π A Γ0 Δ0 HtrΣ Hs0).
        destruct H_prev_inv as [itm [Hin [Hdst Hproj]]].
        rewrite app_length in Hlen.
        simpl in Hlen.
        rewrite Nat.add_1_r in Hlen.
        apply Nat.succ_inj in Hlen.
        pose proof (input_valid_transition_in is0 s0 tr0 HtrΣ itm Hin) as Htrs. 

        destruct Htrs as [tr1 [tr2 [Htrs Hinp]]].
        pose proof HtrΣ as Htrp.
        rewrite Htrs in Htrp.
        rewrite app_assoc in Htrp.
        pose proof (finite_valid_trace_init_to_prefix_1 sequent_vlsm Htrp) as Hpref.
        unfold finite_trace_last in Hpref.
        assert (Hlast: last (map destination (tr1 ++ [itm])) is0 = destination itm).
        {
          rewrite map_app.
          simpl.
          by rewrite last_app.
        }
        rewrite Hlast in Hpref.
        specialize (IHlen_Σ0 Π Hlen is0 (destination itm) (tr1 ++ [itm]) Γ0 (A :: Δ0) Hpref).

        specialize (IHlen_Σ0 Hdst).
        destruct IHlen_Σ0 as [itm_res [Hin_res [Hdst_res Hproj_res]]].
        exists itm_res. repeat split.
        + rewrite Htrs. 
          rewrite app_assoc.
          apply elem_of_app.
          by left.
        + rewrite <- app_assoc.
          by exact Hdst_res.
        + exact Hproj_res.
    }
    cut (derivable_sequent (seq Γ (Σ ++ B :: C :: Δ))).
    + intros [k H_rec].
      unfold derivable_sequent.
      exists (S k).
      exact (SC_XCHG_RIGHT B C Γ Σ Δ k H_rec).
    + specialize (H_prev_capt Σ is s tr Γ (B :: C :: Δ) Htr1 Hse).
      destruct H_prev_capt as [i_capt [Hin_capt [Hdest_capt Hproj_capt]]].
      pose proof (input_valid_transition_in is s tr Htr1 i_capt Hin_capt) as Htrs. 
      destruct Htrs as [tr1 [tr2 [Htrs Hinp]]].

      remember (destination i_capt) as dest_capt.
      remember (input i_capt) as inp_capt.
      remember (l i_capt) as l_capt.
      destruct Hinp as [Hval Htrans].
      destruct l_capt as [idx lb].
      simpl in Hproj_capt.
      subst idx.
      remember (finite_trace_last is tr1) as prev_in.

      simpl in Htrans.
      simpl in Hval.
      destruct Hval as [_ [_ Hval3]].
      destruct lb, (prev_in I_V_XCHG_RIGHT) eqn:in_eq;
      destruct o, l;
      (try contradiction);
      destruct inp_capt as [[Γ' Δ'] | ]; (try contradiction);
      (try destruct s0);

      (try destruct o);
      (try destruct Delta);
      (try destruct Delta);
      (try contradiction);
      injection Htrans as Htrans;
      pose proof (f_equal (fun h => h I_V_XCHG_RIGHT) Htrans) as Hloc;
      simpl in Hloc;
      rewrite state_update_eq in Hloc;
      rewrite Hdest_capt in Hloc;
      inversion Hloc.
      
      subst Γ'.
      subst Δ'.
      symmetry in Heqinp_capt.
      exact (elem_derivable_input tr i_capt (seq  Γ (Σ ++ B :: C :: Δ)) Hin_capt IHHtr1 Heqinp_capt).
Qed.

Theorem vlsm_valid_derivable_sequent : 
  forall (m : Sequent), 
    vlsm_valid_sequent (m) -> 
      derivable_sequent(m).
Proof.
  intros m.
  intros [s Hvsmp].
  
  apply valid_state_message_has_trace in Hvsmp as [(Hisp & H1) | (is & tr & Htr & Hout)].
  
  (* Initial message *)
  - destruct H1 as [idx [mi Hmi]].
    destruct idx, mi, i.

  (* Trace *)
  - pose proof Htr as Htr_full. 
    destruct_list_last tr tr' lst Htr_lst;  destruct Htr as [Htr Hinit].
    by inversion Hout.

    apply finite_valid_trace_from_to_app_split in Htr as [Htr' Hlst].
    remember (finite_trace_last is tr') as s'.
    apply valid_trace_get_last in Hlst as Heqs.

    apply valid_trace_forget_last, first_transition_valid in Hlst.
    cbn in Heqs, Hlst; rewrite Heqs in Hlst.
    rewrite finite_trace_last_output_is_last in Hout.
    cut (trace_messages_derivable_sequents tr).
    + intros Hder.
      simpl in Hout.
      unfold trace_messages_derivable_sequents in Hder.
      specialize (Hder m).
      unfold trace_has_message in Hder.
      apply Hder.
      rewrite Htr_lst.
      apply Exists_app. right.
      apply Exists_cons_hd.
      by right. 
    + rewrite <- Htr_lst in Htr_full.
      exact (all_valid_traces_derivable_sequents Htr_full). 
Qed.

End sec_sequent_calculus.