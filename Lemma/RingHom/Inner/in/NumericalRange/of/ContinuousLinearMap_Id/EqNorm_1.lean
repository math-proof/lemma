import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.ToeplitzHausdorff
open InnerProductSpace.ToeplitzHausdorffWanted


/--
[ToeplitzHausdorff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/ToeplitzHausdorff.lean)
-/
@[path]
private lemma inner_mem_numerical_range_is
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {x : E}
  (hx : ‖x‖ = 1)
  (A : ContinuousLinearMap (RingHom.id ℂ) E E) :
-- imply
  inner (𝕜 := ℂ) (A x) x ∈ numericalRange A := by
-- proof
  apply inner_mem_numericalRange A hx


-- created on 2026-10-10
-- updated on 2026-10-26
