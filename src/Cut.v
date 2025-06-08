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

(** * On the CUT rule  *)

(* ** The CUT rule in GK' *)

Inductive CUT : Sequent -> Prop :=
    | CUT_intro (A : Formula) (Γ1 Δ1 Γ2 Δ2 : list Formula)
                (h1 : nat) (h2 : nat)
                (H1 : SC_derivation h1 (seq (A :: Γ1) Δ1)) 
                (H2 : SC_derivation h2 (seq Γ2 (A :: Δ2))) :

                CUT (seq (Γ1 ++ Γ2) (Δ1 ++ Δ2))
    | CUT_der (s : Sequent) (h : nat) 
              (H : SC_derivation h s) : 
              
              CUT (s).

(** ** VLSM for the CUT rule  *)
Definition V_CUT_label := RecEmitLeftRight.
Definition V_CUT_state := option Sequent.

Definition V_CUT_vlsm_type : VLSMType Sequent :=
  {| label := V_CUT_label;
     state := V_CUT_state; |}.

Definition V_CUT_machine : VLSMMachine V_CUT_vlsm_type :=
  {| initial_state_prop := fun s => s = None;
     s0 := populate (exist _ None eq_refl);
     initial_message_prop := fun m => vlsm_valid_sequent m;

     transition := fun l som =>
       match l, som.1, som.2 with
       | recLeft, None, Some (seq (A :: Γ) Δ) =>
           (Some (seq (A :: Γ) Δ), None)
       | recRight, None, Some (seq Γ (A :: Δ)) =>
           (Some (seq Γ (A :: Δ)), None)
       | emitLeft, Some (seq (A :: Γ1) Δ1), Some (seq Γ2 (A' :: Δ2)) =>
           if decide (A = A') then (None, Some (seq (Γ1 ++ Γ2) (Δ1 ++ Δ2)))
           else (None, None)
       | emitRight, Some (seq Γ2 (A :: Δ2)), Some (seq (A' :: Γ1) Δ1) =>
           if decide (A = A') then (None, Some (seq (Γ1 ++ Γ2) (Δ1 ++ Δ2)))
           else (None, None)
       | _, _, _ => (None, None)
       end;

     valid := fun l som =>
       match l, som.1, som.2 with
       | recLeft, None, Some (seq (A :: Γ) Δ) => vlsm_valid_sequent(seq (A :: Γ) Δ)
       | recRight, None, Some (seq Γ (A :: Δ)) => vlsm_valid_sequent(seq Γ (A :: Δ))
       | emitLeft, Some (seq (A :: Γ) Δ), Some (seq Γ' (A' :: Δ')) => 
            if decide (A = A') then vlsm_valid_sequent(seq  Γ' (A :: Δ')) 
            else False
       | emitRight, Some (seq Gamma' (A :: Δ')), Some (seq (A' :: Γ) Δ) =>
            if decide (A = A') then vlsm_valid_sequent(seq (A' :: Γ) Δ) 
            else False
       | _, _, _ => False
       end; |}.

Definition V_CUT : VLSM Sequent :=
    mk_vlsm V_CUT_machine.

Definition cut_valid_sequent (s : Sequent) : Prop :=
    valid_message_prop V_CUT s.

(** ** Soundness *)
Theorem CUT_rule_vlsm :
    forall (s : Sequent),
        CUT s -> cut_valid_sequent s.

Proof.
    intros s.
    intros Hcut.
    destruct Hcut as [A Γ1 Δ1 Γ2 Δ2 h1 h2 H1 H2 | s h H].
    - assert (H1_vlsm: vlsm_valid_sequent (seq (A :: Γ1) Δ1)).
      {
         apply derivable_sequents_vlsm_valid.
         by exists h1.
      }

      assert (H2_vlsm: vlsm_valid_sequent (seq Γ2 (A :: Δ2))).
      {
          apply derivable_sequents_vlsm_valid.
          by exists h2.
      }
        
      assert (Ht1: input_valid_transition V_CUT recLeft (None, Some (seq (A :: Γ1) Δ1)) (Some (seq (A :: Γ1) Δ1), None)).
      {
          repeat split.
          - by apply initial_state_is_valid. 
          - by apply initial_message_is_valid.
          - by destruct V_CUT_machine.
      }

      cut (input_valid_transition V_CUT emitLeft (Some (seq (A :: Γ1) Δ1), Some (seq Γ2 (A :: Δ2))) (None, Some (seq (Γ1 ++ Γ2) (Δ1 ++ Δ2))));
            [by eapply input_valid_transition_out |].
        repeat split.
        + by eapply input_valid_transition_destination.
        + apply initial_message_is_valid.
        by unfold V_CUT; simpl; destruct V_CUT_machine.
        + simpl.
          destruct (decide (A = A)).
          * auto.
          * contradiction.
        + simpl.
          destruct (decide (A = A)).
          * auto.
          * contradiction.
    - apply emitted_messages_are_valid_iff.
      left. simpl.
      destruct s as [Γ Δ].
      apply derivable_sequents_vlsm_valid.
      by exists h.

Qed.

(** ** Completeness *)

(** Helper lemma: captured sequents are derivable  *)

Lemma CUT_state_derivable :
    forall (s : Sequent),
        valid_state_prop V_CUT (Some s) -> derivable_sequent s.
Proof.
    intros s.
    intros Hvstate.
    simpl in Hvstate.
    destruct Hvstate as [m Hm].
    apply (option_can_produce_valid_iff V_CUT) in Hm.
    destruct Hm.
    - destruct H as [[s' m'] [l H]].
      destruct H as [H1 H2].
      simpl in H1.
      simpl in H2.
      destruct H1 as [_ [_ H1]].
      destruct l, s'; (try contradiction).
      + destruct m'; [| contradiction].
        destruct s0, Gamma. contradiction.
        inversion H2.
        subst.
        by apply vlsm_valid_derivable_sequent in H1.
      + destruct m'; [| contradiction].
        destruct s0, Delta. contradiction.
        inversion H2.
        subst.
        by apply vlsm_valid_derivable_sequent in H1.
      + destruct s0, Gamma. contradiction.
        destruct m'; [| contradiction].
        destruct s0, Delta0. contradiction.
        destruct (decide (f = f0)) as [Hdec | Hdec]; inversion H2.
      + destruct s0, Delta. contradiction.
        destruct m'; [| contradiction].
        destruct s0, Gamma0. contradiction.
        destruct (decide (f = f0)) as [Hdec | Hdec]; inversion H2.
    - by destruct H as [H _].
Qed.


Theorem vlsm_CUT_rule:
    forall (s : Sequent),
        cut_valid_sequent s -> CUT s.
Proof.
    intros s.
    intros HcutVLSM.
    pose proof (emitted_messages_are_valid_iff V_CUT s) as Hvm.
    destruct Hvm as [Hvm1 _].
    specialize (Hvm1 HcutVLSM).
    destruct Hvm1.
    - simpl in H.
      apply vlsm_valid_derivable_sequent in H.
      destruct H as [h Hder].
      exact (CUT_der s h Hder).
    - unfold can_emit in H.
      destruct H as [som [l [s0 H]]].
      destruct H as [Hvalid Htrans].
      simpl in Htrans.
      destruct l, som as [[s1 | ] [m1 | ]]; 
      simpl in Htrans, Hvalid; (try (inversion Htrans)).
      + destruct m1, Gamma; by inversion Htrans.
      + destruct m1, Delta; by inversion Htrans.
      + destruct s1 eqn:Heq_s1, Gamma; [by inversion Htrans| ].
        destruct m1, Delta0; [by inversion Htrans| ].
        destruct (decide (f = f0)) as [Hdec | Hdec]; inversion Htrans.
        destruct Hvalid as [Hvalid1 [_ Hvalid3]].
        pose proof (CUT_state_derivable s1) as Hcut_val.
        subst.
        apply Hcut_val in Hvalid1.
        apply vlsm_valid_derivable_sequent in Hvalid3.
        destruct Hvalid1 as [h1 Hder1].
        destruct Hvalid3 as [h2 Hder2].
        exact (CUT_intro f0 Gamma Delta Gamma0 Delta0 h1 h2 Hder1 Hder2).
      + destruct s1, Gamma; inversion Htrans.
      + destruct s1 eqn:Heq_s1, Delta. inversion Htrans.
        destruct m1, Gamma0. by destruct Hvalid.
        destruct (decide (f = f0)); destruct Hvalid as [Hvalid1 [_ Hvalid3]]; [| contradiction].
        pose proof (CUT_state_derivable s1) as Hcut_val.
        inversion Htrans.
        subst.
        apply Hcut_val in Hvalid1.
        apply vlsm_valid_derivable_sequent in Hvalid3.
        destruct Hvalid1 as [h1 Hder1].
        destruct Hvalid3 as [h2 Hder2].
        exact (CUT_intro f0 Gamma0 Delta0 Gamma Delta  h2 h1 Hder2 Hder1).
      + destruct s1, Delta; inversion Htrans.
Qed.
