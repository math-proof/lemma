import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.ToeplitzHausdorff
open InnerProductSpace.ToeplitzHausdorffWanted


/--
[ToeplitzHausdorff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/ToeplitzHausdorff.lean)
-/
@[path]
private lemma mem_numerical_range_iff
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (A : ContinuousLinearMap (RingHom.id ℂ) E E)
  (c : ℂ) :
-- imply
  c ∈ numericalRange A ↔ ∃ x : E, ‖x‖ = 1 ∧ inner (𝕜 := ℂ) (A x) x = c := by
-- proof
  apply mem_numericalRange_iff


-- created on 2026-10-10
-- updated on 2026-10-24
