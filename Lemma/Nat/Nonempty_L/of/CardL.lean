import Mathlib
import sympy.Basic


/--
[FiniteField_nonempty_algEquiv_of_card_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FiniteField_nonempty_algEquiv_of_card_eq.lean)
-/
@[main]
private lemma main
  [Field K] [Field L₁] [Algebra K L₁] [Finite L₁] [Field L₂] [Algebra K L₂] [Finite L₂]
-- given
  (h : Nat.card L₁ = Nat.card L₂) :
-- imply
  Nonempty (L₁ ≃ₐ[K] L₂) := by
-- proof
  classical
  haveI := Fintype.ofFinite L₁
  haveI := Fintype.ofFinite L₂
  have h' : Fintype.card L₁ = Fintype.card L₂ := by
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  haveI i₁ : Polynomial.IsSplittingField K L₁ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X) :=
    FiniteField.isSplittingField_sub L₁ K
  haveI i₂ : Polynomial.IsSplittingField K L₂ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X) := by
    rw [h']; exact FiniteField.isSplittingField_sub L₂ K
  exact ⟨(Polynomial.IsSplittingField.algEquiv L₁ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X)).trans
    (Polynomial.IsSplittingField.algEquiv L₂ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X)).symm⟩


-- created on 2026-10-05
