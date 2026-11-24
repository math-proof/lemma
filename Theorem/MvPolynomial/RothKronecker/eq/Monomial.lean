module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.NumberTheory.RothAuxiliary.Part7
open MathlibExt.NumberTheory.RothAuxiliary


public section

/--
[rothKronecker_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  {m : ℕ} [Field K] (D : ℕ)
  (i : Finsupp (Fin m) ℕ) (c : K) :
-- imply
  rothKronecker D (MvPolynomial.monomial i c) =
    Polynomial.monomial (rothKroneckerEncode D fun h ↦ i h) c := by
-- proof
  rw [rothKronecker, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  congr 1
  unfold rothKroneckerEncode
  calc
    _ = ∑ a : Fin m, D ^ (a : ℕ) * i a := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ hnot
      have hai : i a = 0 := by simpa using hnot
      simp [hai]
    _ = ∑ a : Fin m, i a * D ^ (a : ℕ) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Nat.mul_comm


-- created on 2026-10-21
-- updated on 2026-11-15
