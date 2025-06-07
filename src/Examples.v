From stdpp Require Import prelude.
From VLSM.Core Require Import VLSM Composition ProjectionTraces.
From VLSM_SC Require Import Sequents.
From VLSM_SC Require Import SequentsVLSM.

Import Form.
Import Calculus.

#[local] Notation "⊤" := FTop.
#[local] Notation "⊥" := FBot.
#[local] Notation "x ∨ y" := (FDisj x y) (at level 85, right associativity).
#[local] Notation "x ∧ y" := (FConj x y) (at level 80, right associativity).
#[local] Notation "x → y" := (FImpl x y) (at level 99, y at level 200, right associativity).

(** * Examples *)

(** ** The derivation of Peirce's Law in GK' *)

Example derivable_peirce :
    forall (A B : Formula), derivable_sequent(seq [] [((A→B)→A)→A]).
Proof.
    intros A B.
    exists 5.
    apply SC_IMP_RIGHT.
    apply SC_CT_RIGHT.
    cut (SC_derivation 0 (seq [A] [A])).
    - intros HAID.
      apply (SC_IMP_LEFT (A→B) A [] [] [A] [A] 2 0).
      + apply SC_IMP_RIGHT.
        by apply SC_WK_RIGHT.
      + exact HAID.
    - apply SC_ID.
Qed.

(** ** The valid VLSM trace of Peirce's Law *)

Definition peirce_trace_pref (A B : Formula) : list (transition_item sequent_vlsm) :=
    [@Build_transition_item Sequent sequent_vlsm (existT I_V_ID A) (None) s0_seq (Some (seq [A] [A]));
     @Build_transition_item Sequent sequent_vlsm (existT I_V_WK_RIGHT B) (Some (seq [A] [A])) s0_seq (Some (seq [A] [B; A]));
     @Build_transition_item Sequent sequent_vlsm (existT I_V_IMP_RIGHT ()) (Some (seq [A] [B; A])) s0_seq (Some (seq [] [A→B; A]));
     @Build_transition_item Sequent sequent_vlsm (existT I_V_IMP_LEFT recLeft) (Some (seq [A] [A])) 
        (state_update sequent_vlsm_components s0_seq I_V_IMP_LEFT (Some (seq [A] [A])) ) (None);
     @Build_transition_item Sequent sequent_vlsm (existT I_V_IMP_LEFT emitLeft) (Some (seq [] [A→B; A])) s0_seq (Some (seq [(A→B)→A] [A; A]));
     @Build_transition_item Sequent sequent_vlsm (existT I_V_CT_RIGHT ()) (Some (seq [(A→B)→A] [A; A])) s0_seq (Some (seq [(A→B)→A] [A]))
    ].

Definition peirce_trace_last (A B : Formula): transition_item sequent_vlsm :=
     @Build_transition_item Sequent sequent_vlsm (existT I_V_IMP_RIGHT ()) (Some (seq [(A→B)→A] [A])) s0_seq (Some (seq [] [((A→B)→A)→A])).

Definition peirce_trace (A B : Formula) : list (transition_item sequent_vlsm) :=
    peirce_trace_pref A B ++ [peirce_trace_last A B].

Lemma s0_seq_initial :
    initial_state_prop sequent_vlsm s0_seq.
Proof.
    unfold s0_seq.
    by destruct composite_s0.
Qed.

Proposition valid_trans_peirce_1 : 
    forall (A : Formula), 
        input_valid_transition sequent_vlsm (existT I_V_ID A) (s0_seq, None) (s0_seq, Some (seq [A] [A])).
    Proof.
    intros A.
    repeat split.
    - apply initial_state_is_valid.
      exact s0_seq_initial.
    - apply option_valid_message_None.
    - by simpl; rewrite state_update_id.
Qed.

Proposition valid_trans_peirce_2 : 
    forall (A B : Formula), 
        input_valid_transition sequent_vlsm (existT I_V_WK_RIGHT B) (s0_seq, Some (seq [A] [A])) (s0_seq, Some (seq [A] [B; A])).
Proof.
    intros A B.
    repeat split.
    - apply initial_state_is_valid. exact s0_seq_initial.
    - app_valid_tran.
      exists (s0_seq, None). exists (existT I_V_ID A). exists s0_seq.
      exact (valid_trans_peirce_1 A).
    - simpl. rewrite state_update_id.
        + reflexivity.
        + auto.
Qed.

Proposition valid_trans_peirce_3 : 
    forall (A B : Formula), 
        input_valid_transition sequent_vlsm (existT I_V_IMP_RIGHT ()) (s0_seq, Some (seq [A] [B; A])) (s0_seq, Some (seq [] [A→B; A])).
Proof.
    intros A B.
    repeat split.
    - apply initial_state_is_valid. exact s0_seq_initial.
    - app_valid_tran. 
      exists (s0_seq, Some (seq [A] [A])). exists (existT I_V_WK_RIGHT B). exists s0_seq.
      exact (valid_trans_peirce_2 A B).
    - simpl. rewrite state_update_id.
        + reflexivity.
        + auto.
Qed.

Proposition valid_trans_peirce_4:
    forall (A : Formula),
      input_valid_transition sequent_vlsm (existT I_V_IMP_LEFT recLeft) (s0_seq, Some (seq [A] [A])) 
        (state_update sequent_vlsm_components s0_seq I_V_IMP_LEFT (Some (seq [A] [A])), None).
Proof. 
    intros A.
    repeat split.
    - apply initial_state_is_valid. exact s0_seq_initial.
    - app_valid_tran.
      exists (s0_seq, None). exists (existT I_V_ID A). exists s0_seq.
      exact (valid_trans_peirce_1 A).
Qed.

Proposition valid_trans_peirce_5:
  forall (A B : Formula),
    input_valid_transition sequent_vlsm (existT I_V_IMP_LEFT emitLeft) 
      ((state_update sequent_vlsm_components s0_seq I_V_IMP_LEFT (Some (seq [A] [A])) ), Some (seq [] [A→B; A])) 
      (s0_seq, Some (seq [(A→B)→A] [A; A])).
Proof.
  intros A B.
  repeat split.
  - exact (input_valid_transition_destination sequent_vlsm (valid_trans_peirce_4 A)).
  - exact (input_valid_transition_out sequent_vlsm (valid_trans_peirce_3 A B)). 
  - simpl.
    by rewrite state_update_eq.
  - simpl.
    rewrite state_update_eq. rewrite state_update_twice.
    by rewrite state_update_id.
Qed.

Proposition valid_trans_peirce_6:
  forall (A B : Formula),
    input_valid_transition sequent_vlsm (existT I_V_CT_RIGHT ()) 
      (s0_seq, Some (seq [(A→B)→A] [A; A])) (s0_seq, Some (seq [(A→B)→A] [A])).
Proof.
  intros A B.
  repeat split.
  - apply initial_state_is_valid. exact s0_seq_initial.
  - exact (input_valid_transition_out sequent_vlsm (valid_trans_peirce_5 A B)).
  - simpl. destruct (decide (A = A)).
    + subst. reflexivity.
    + exfalso. apply n. reflexivity.
  - simpl.
    destruct (decide (A = A)); rewrite state_update_id.
      + reflexivity.
      + auto.
      + exfalso. apply n. reflexivity.
      + done.
Qed.

Proposition valid_trans_peirce_7:
  forall (A B : Formula),
    input_valid_transition sequent_vlsm (existT I_V_IMP_RIGHT ()) 
      (s0_seq, Some (seq [(A→B)→A] [A])) (s0_seq, Some (seq [] [((A→B)→A)→A])).
Proof.
  intros A B.
  repeat split.
  - apply initial_state_is_valid. exact s0_seq_initial.
  - exact (input_valid_transition_out sequent_vlsm (valid_trans_peirce_6 A B)).
  - simpl. rewrite state_update_id.
      + reflexivity.
      + auto.
Qed.

Example peirce_trace_valid : 
    forall (A B : Formula), 
        finite_valid_trace_init_to sequent_vlsm s0_seq s0_seq (peirce_trace A B).
Proof.
    intros A B.
    constructor; [| exact s0_seq_initial].
    repeat apply finite_valid_trace_from_to_extend.
    - apply finite_valid_trace_from_to_empty.
      apply initial_state_is_valid. 
      exact s0_seq_initial.
      
    - exact (valid_trans_peirce_7 A B).
    - exact (valid_trans_peirce_6 A B).
    - exact (valid_trans_peirce_5 A B).
    - exact (valid_trans_peirce_4 A).
    - exact (valid_trans_peirce_3 A B).
    - exact (valid_trans_peirce_2 A B).
    - exact (valid_trans_peirce_1 A).
Qed.


