From Coq Require Import FunctionalExtensionality.
From stdpp Require Import prelude.
From VLSM.Lib Require Import ListExtras.
From VLSM.Core Require Import VLSM Composition ProjectionTraces.
From VLSM_SC Require Import Sequents.

Require Import Coq.Lists.List.
Require Import Wellfounded.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Lt. 

Import Form.
Import Calculus.

(** * Sequent Calculus VLSMs *)

(** This module defines the structure of sequents and the VLSMs for the identity and bottom rules of sequent calculus. *)

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
| exchange
| append
| emitX.


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
  {| initial_state_prop := fun _ => True;
     s0 := populate (exist _ None I); (* Initial state with empty Gamma and Delta *)
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
  {| initial_state_prop := fun _ => True;
     s0 := populate (exist _ None I);
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
       | exchange, (Γ, Some (seq (B :: C :: Π) Δ)), None => (([], None), Some (seq (Γ ++ C :: B :: Π) Δ))
       | _, _, _ => (([], None), None)
       end;

     valid := fun l som =>
       match l, som.1, som.2 with
       | recX, ([], None), Some (seq Γ Δ) => True
       | extract, (Γ, Some (seq (A :: Π) Δ)), None => True
       | exchange, (Γ, Some (seq (B :: C :: Π) Δ)), None => True
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
       | exchange, (Γ, Some (seq Δ (B :: C :: Π))), None => (([], None), Some (seq Δ (Γ ++ C :: B :: Π)))
       | _, _, _ => (([], None), None)
       end;

     valid := fun l som => 
       match l, som.1, som.2 with
       | recX, ([], None), Some (seq Γ Δ) => True
       | extract, (Γ, Some (seq Δ (A :: Π) )), None => True
       | exchange, (Γ, Some (seq Δ (B :: C :: Π))), None => True
       | _, _, _ => False
       end;
       |}.

Definition V_XCHG_RIGHT : VLSM Sequent := 
  mk_vlsm V_XCHG_RIGHT_machine.

(*TODO: Create cutfree composition*)
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
  cut (input_valid_transition sequent_vlsm (existT I_V_XCHG_LEFT exchange) 
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
  cut (input_valid_transition sequent_vlsm (existT I_V_XCHG_RIGHT exchange) 
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

End sec_sequent_calculus.
