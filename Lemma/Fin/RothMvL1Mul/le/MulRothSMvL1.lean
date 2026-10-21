import Mathlib
import Lemma.Fin.RothMvL1_Sum.le.Sum_RothMvL1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P Q : MvPolynomial (Fin m) ℤ) :
-- imply
  rothMvL1 (P * Q) ≤ rothMvL1 P * rothMvL1 Q := by
-- proof
  classical
  have hmono (i : RothMvIndex m) (c : ℤ) :
    rothMvL1 (MvPolynomial.monomial i c) = c.natAbs := by
    change rothFinsuppL1 (Finsupp.single i c) = c.natAbs
    if hc : c = 0 then
      simp [hc, rothFinsuppL1]
    else
      simp [rothFinsuppL1, hc]
  rw [MvPolynomial.mul_def, Finsupp.sum]
  calc
    _ ≤ ∑ a ∈ P.support,
        rothMvL1 (Q.coeff.sum fun b d ↦ MvPolynomial.monomial (a + b) (P.coeff a * d)) :=
      RothMvL1_Sum.le.Sum_RothMvL1 P.support _
    _ = ∑ a ∈ P.support,
        rothMvL1 (∑ b ∈ Q.support, MvPolynomial.monomial (a + b) (P.coeff a * Q.coeff b)) := by
      congr with a
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support,
        rothMvL1 (MvPolynomial.monomial (a + b) (P.coeff a * Q.coeff b)) := by
      gcongr with a _
      exact RothMvL1_Sum.le.Sum_RothMvL1 Q.support _
    _ = ∑ a ∈ P.support, (P.coeff a).natAbs * rothMvL1 Q := by
      congr with a
      simp_rw [hmono, Int.natAbs_mul]
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support, ← Finset.mul_sum]
    _ = rothMvL1 P * rothMvL1 Q := by
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support, Finset.sum_mul]


-- created on 2026-10-21
