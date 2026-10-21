import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.RothPolyL1.eq.Sum_NatAbsCoeff
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_le_natDegree_succ_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P : ℤ[X])
  (H : ℕ)
-- given
  (hcoeff : ∀ n, (P.coeff n).natAbs ≤ H) :
-- imply
  rothPolyL1 P ≤ (P.natDegree + 1) * H := by
-- proof
  rw [RothPolyL1.eq.Sum_NatAbsCoeff]
  calc
    _ ≤ ∑ _ ∈ P.support, H := by
      gcongr with n
      apply hcoeff n
    _ = P.support.card * H := by simp
    _ ≤ (P.natDegree + 1) * H := by
      gcongr
      simpa using Finset.card_le_card supp_subset_range_natDegree_succ


-- created on 2026-10-21
