From stdpp Require Import prelude.
Context 
  `{EqDecision Var}
  `{base.Infinite Var}.
  
Module Export Form.

Inductive symbol : Type :=
| Top
| Bot
| PVar (x : Var)
| Conj
| Disj
| Impl.


#[export] Instance symbol_dec : EqDecision symbol.
Proof.
  unfold EqDecision, Decision; decide equality.
  by destruct (decide (x0 = x1)); [left | right].
Qed.

Definition expression : Type := list symbol.

Inductive Formula : Type :=
| FTop
| FBot
| FVar (x : Var)
| FConj (f1 f2 : Formula)
| FDisj (f1 f2 : Formula)
| FImpl (f1 f2 : Formula).

#[export] Instance formula_dec : EqDecision Formula.
Proof. unfold EqDecision. unfold Decision. decide equality.
       by destruct (decide (x0 = x1)); [left | right].
Qed.

Definition list_formula_eq (l1 l2 : list Formula) : bool :=
    if decide (l1 = l2) then true else false.

End Form.

Module Calculus.

#[local] Notation "⊤" := FTop.
#[local] Notation "⊥" := FBot.
#[local] Notation "x ∨ y" := (FDisj x y) (at level 85, right associativity).
#[local] Notation "x ∧ y" := (FConj x y) (at level 80, right associativity).
#[local] Notation "x → y" := (FImpl x y) (at level 99, y at level 200, right associativity).

Inductive Sequent : Type :=
| seq (Gamma Delta : list Formula) : Sequent.


Inductive SC_derivation : nat -> Sequent -> Prop :=
  | SC_ID (A : Formula) : SC_derivation 0 (seq [A] [A])
  | SC_BOT : SC_derivation 0 (seq [⊥] [])
  | SC_TOP : SC_derivation 0 (seq [] [⊤])
  | SC_IMP_RIGHT (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : SC_derivation h (seq (A :: Γ) (B :: Δ))) :
      SC_derivation (S h) (seq Γ ((A → B) :: Δ))
  | SC_IMP_LEFT (A B : Formula) (Γ1 Γ2 Δ1 Δ2 : list Formula) (h1 h2 : nat)
      (Hd1 : SC_derivation h1 (seq Γ1 (A :: Δ1)))
      (Hd2 : SC_derivation h2 (seq (B :: Γ2) Δ2)) :
      SC_derivation (S (max h1 h2)) (seq ((A → B) :: Γ1 ++ Γ2) (Δ1 ++ Δ2))
  | SC_CONJ_LEFT_1 (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : SC_derivation h (seq (A :: Γ) Δ)) :
      SC_derivation (S h) (seq ((A ∧ B) :: Γ) Δ)
  | SC_CONJ_LEFT_2 (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : SC_derivation h (seq (A :: Γ) Δ)) :
      SC_derivation (S h) (seq ((B ∧ A) :: Γ) Δ)
  | SC_CONJ_RIGHT (A B : Formula) (Γ Δ : list Formula) (h1 h2 : nat)
      (Hd1 : SC_derivation h1 (seq Γ (A :: Δ)))
      (Hd2 : SC_derivation h2 (seq Γ (B :: Δ))) :
      SC_derivation (S (max h1 h2)) (seq Γ ((A ∧ B) :: Δ))
  | SC_DISJ_LEFT (A B : Formula) (Γ Δ : list Formula) (h1 h2 : nat)
      (Hd1 : SC_derivation h1 (seq (A :: Γ) Δ))
      (Hd2 : SC_derivation h2 (seq (B :: Γ) Δ)) :
      SC_derivation (S (max h1 h2)) (seq ((A ∨ B) :: Γ) Δ)
  | SC_DISJ_RIGHT_1 (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : SC_derivation h (seq Γ (A :: Δ))) :
      SC_derivation (S h) (seq Γ ((A ∨ B) :: Δ))
  | SC_DISJ_RIGHT_2 (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : SC_derivation h (seq Γ (A :: Δ))) :
      SC_derivation (S h) (seq Γ ((B ∨ A) :: Δ))
  | SC_WK_LEFT (A : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : SC_derivation h (seq Γ Δ)) :
      SC_derivation (S h) (seq (A :: Γ) Δ)
  | SC_WK_RIGHT (A : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : SC_derivation h (seq Γ Δ)) :
      SC_derivation (S h) (seq Γ (A :: Δ))
  | SC_CT_RIGHT (A : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : SC_derivation h (seq Γ (A :: A :: Δ))) :
      SC_derivation (S h) (seq Γ (A :: Δ))
  | SC_CT_LEFT (A : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : SC_derivation h (seq (A :: A :: Γ) Δ)) :
      SC_derivation (S h) (seq (A :: Γ) Δ)
  | SC_XCHG_LEFT (A B : Formula) (Γ Δ Π : list Formula) (h : nat)
      (Hd : SC_derivation h (seq (Γ ++ A :: B :: Π) Δ)) :
      SC_derivation (S h) (seq (Γ ++ B :: A :: Π) Δ)
  | SC_XCHG_RIGHT (A B : Formula) (Γ Δ Π : list Formula) (h : nat)
      (Hd : SC_derivation h (seq Γ (Δ ++ A :: B :: Π))) :
      SC_derivation (S h) (seq Γ (Δ ++ B :: A :: Π)).


Inductive GK_derivation : nat -> Sequent -> Prop :=
  | GK_ID (A : Formula) : GK_derivation 0 (seq [A] [A])
  | GK_BOT (Γ Δ: list Formula) : GK_derivation 0 (seq (⊥ :: Γ) Δ)
  | GK_TOP (Γ Δ: list Formula) : GK_derivation 0 (seq Γ (⊤ :: Δ))
  | GK_IMP_RIGHT (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : GK_derivation h (seq (A :: Γ) (B :: Δ))) :
      GK_derivation (S h) (seq Γ ((A → B) :: Δ))
  | GK_IMP_LEFT (A B : Formula) (Γ1 Γ2 Δ1 Δ2 : list Formula) (h1 h2 : nat)
      (Hd1 : GK_derivation h1 (seq Γ1 (A :: Δ1)))
      (Hd2 : GK_derivation h2 (seq (B :: Γ2) Δ2)) :
      GK_derivation (S (max h1 h2)) (seq ((A → B) :: Γ1 ++ Γ2) (Δ1 ++ Δ2))
  | GK_CONJ_LEFT_1 (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : GK_derivation h (seq (A :: Γ) Δ)) :
      GK_derivation (S h) (seq ((A ∧ B) :: Γ) Δ)
  | GK_CONJ_LEFT_2 (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : GK_derivation h (seq (A :: Γ) Δ)) :
      GK_derivation (S h) (seq ((B ∧ A) :: Γ) Δ)
  | GK_CONJ_RIGHT (A B : Formula) (Γ Δ : list Formula) (h1 h2 : nat)
      (Hd1 : GK_derivation h1 (seq Γ (A :: Δ)))
      (Hd2 : GK_derivation h2 (seq Γ (B :: Δ))) :
      GK_derivation (S (max h1 h2)) (seq Γ ((A ∧ B) :: Δ))
  | GK_DISJ_LEFT (A B : Formula) (Γ Δ : list Formula) (h1 h2 : nat)
      (Hd1 : GK_derivation h1 (seq (A :: Γ) Δ))
      (Hd2 : GK_derivation h2 (seq (B :: Γ) Δ)) :
      GK_derivation (S (max h1 h2)) (seq ((A ∨ B) :: Γ) Δ)
  | GK_DISJ_RIGHT_1 (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : GK_derivation h (seq Γ (A :: Δ))) :
      GK_derivation (S h) (seq Γ ((A ∨ B) :: Δ))
  | GK_DISJ_RIGHT_2 (A B : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : GK_derivation h (seq Γ (A :: Δ))) :
      GK_derivation (S h) (seq Γ ((B ∨ A) :: Δ))
  | GK_WK_LEFT (A : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : GK_derivation h (seq Γ Δ)) :
      GK_derivation (S h) (seq (A :: Γ) Δ)
  | GK_WK_RIGHT (A : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : GK_derivation h (seq Γ Δ)) :
      GK_derivation (S h) (seq Γ (A :: Δ))
  | GK_CT_RIGHT (A : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : GK_derivation h (seq Γ (A :: A :: Δ))) :
      GK_derivation (S h) (seq Γ (A :: Δ))
  | GK_CT_LEFT (A : Formula) (Γ Δ : list Formula) (h : nat)
      (Hd : GK_derivation h (seq (A :: A :: Γ) Δ)) :
      GK_derivation (S h) (seq (A :: Γ) Δ)
  | GK_XCHG_LEFT (A B : Formula) (Γ Δ Π : list Formula) (h : nat)
      (Hd : GK_derivation h (seq (Γ ++ A :: B :: Π) Δ)) :
      GK_derivation (S h) (seq (Γ ++ B :: A :: Π) Δ)
  | GK_XCHG_RIGHT (A B : Formula) (Γ Δ Π : list Formula) (h : nat)
      (Hd : GK_derivation h (seq Γ (Δ ++ A :: B :: Π))) :
      GK_derivation (S h) (seq Γ (Δ ++ B :: A :: Π)).

Lemma SC_is_GK : forall (k : nat) (Γ Δ : list Formula), 
    SC_derivation k (seq Γ Δ) -> 
        exists (k' : nat), GK_derivation k' (seq Γ Δ).
Proof. 
    intros. 
    induction H0.
    - exists 0.
      exact (GK_ID A).
    - exists 0.
      apply GK_BOT.
    - exists 0.
      apply GK_TOP.
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_IMP_RIGHT _ _ _ _ _ H1).
    - destruct IHSC_derivation1.
      destruct IHSC_derivation2.
      exists (S (max x x0)).
      exact (GK_IMP_LEFT _ _ _ _ _ _ _ _ H0 H1).
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_CONJ_LEFT_1 _ _ _ _ _ H1).
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_CONJ_LEFT_2 _ _ _ _ _ H1).
    - destruct IHSC_derivation1.
      destruct IHSC_derivation2.
      exists (S (max x x0)).
      exact (GK_CONJ_RIGHT _ _ _ _ _ _ H0 H1).
    - destruct IHSC_derivation1.
      destruct IHSC_derivation2.
      exists (S (max x x0)).
      exact (GK_DISJ_LEFT _ _ _ _ _ _ H0 H1).
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_DISJ_RIGHT_1 _ _ _ _ _ H1).
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_DISJ_RIGHT_2 _ _ _ _ _ H1).
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_WK_LEFT _ _ _ _ H1).
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_WK_RIGHT _ _ _ _ H1).
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_CT_RIGHT _ _ _ _ H1).
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_CT_LEFT _ _ _ _ H1).
    - destruct IHSC_derivation.
      exists (S x).
      exact (GK_XCHG_LEFT _ _ _ _ _ _ H1).
    - destruct IHSC_derivation. 
      exists (S x).
      exact (GK_XCHG_RIGHT _ _ _ _ _ _ H1).
Qed.

Lemma GK_is_SC : forall (k : nat) (Γ Δ : list Formula), 
    GK_derivation k (seq Γ Δ) -> 
        exists (k' : nat), SC_derivation k' (seq Γ Δ).
Proof.
    intros.
    induction H0.
    - exists 0.
      exact (SC_ID A).
    - induction Γ0.
      + induction Δ0.
        * exists 0.
          exact (SC_BOT).
        * destruct IHΔ0.
          exists (S x).
          exact (SC_WK_RIGHT _ _ _ _ H0).
      + destruct IHΓ0.
        exists (S (S x)).
        apply (SC_XCHG_LEFT a ⊥ []).
        simpl.
        by apply (SC_WK_LEFT).
    - induction Γ0.
      + induction Δ0.
        * exists 0.
          exact (SC_TOP).
        * destruct IHΔ0.
          exists (S (S x)).
          apply (SC_XCHG_RIGHT a ⊤ [] []).
          simpl.
          exact (SC_WK_RIGHT _ _ _ _ H0).
      + destruct IHΓ0.
        exists (S x).
        simpl.
        by apply (SC_WK_LEFT).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_IMP_RIGHT _ _ _ _ _ H1).
    - destruct IHGK_derivation1.
      destruct IHGK_derivation2.
      exists (S (max x x0)).
      exact (SC_IMP_LEFT _ _ _ _ _ _ _ _ H0 H1).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_CONJ_LEFT_1 _ _ _ _ _ H1).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_CONJ_LEFT_2 _ _ _ _ _ H1).
    - destruct IHGK_derivation1.
      destruct IHGK_derivation2.
      exists (S (max x x0)).
      exact (SC_CONJ_RIGHT _ _ _ _ _ _ H0 H1).
    - destruct IHGK_derivation1.
      destruct IHGK_derivation2.
      exists (S (max x x0)).
      exact (SC_DISJ_LEFT _ _ _ _ _ _ H0 H1).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_DISJ_RIGHT_1 _ _ _ _ _ H1).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_DISJ_RIGHT_2 _ _ _ _ _  H1).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_WK_LEFT _ _ _ _ H1).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_WK_RIGHT _ _ _ _ H1).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_CT_RIGHT _ _ _ _ H1).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_CT_LEFT _ _ _ _ H1).
    - destruct IHGK_derivation.
      exists (S x).
      exact (SC_XCHG_LEFT _ _ _ _ _ _ H1).
    - destruct IHGK_derivation. 
      exists (S x).
      exact (SC_XCHG_RIGHT _ _ _ _ _ _ H1).
Qed.

Lemma SC_equiv_GK :  forall (Γ Δ : list Formula), (exists (k : nat), SC_derivation k (seq Γ Δ)) <-> exists (k' : nat), GK_derivation k' (seq Γ Δ).
Proof.
    intros.
    split.
    - intros [k H].
      by apply (SC_is_GK k).
    - intros [k H].
      by apply (GK_is_SC k).
Qed.

End Calculus.

