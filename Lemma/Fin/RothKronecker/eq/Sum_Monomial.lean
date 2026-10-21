import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothKronecker_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [Field K]
  (D : ℕ) (P : MvPolynomial (Fin m) K) :
-- imply
  rothKronecker D P =
    ∑ i ∈ P.support,
      Polynomial.monomial (rothKroneckerEncode D fun h ↦ i h) (P.coeff i) := by
-- proof
  have rothKronecker_monomial (i : RothMvIndex m) (c : K) :
    rothKronecker D (MvPolynomial.monomial i c) =
      Polynomial.monomial (rothKroneckerEncode D fun h ↦ i h) c := by
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
        exact Nat.mul_comm _ _
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply rothKronecker_monomial


-- created on 2026-10-21
