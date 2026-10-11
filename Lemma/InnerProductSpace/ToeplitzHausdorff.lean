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
  apply InnerProductSpace.ToeplitzHausdorffWanted.mem_numericalRange_iff

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
  apply InnerProductSpace.ToeplitzHausdorffWanted.inner_mem_numericalRange A hx

/--
[ToeplitzHausdorff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/ToeplitzHausdorff.lean)
-/
@[path]
private lemma toeplitz_hausdorff_general_is
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (A : ContinuousLinearMap (RingHom.id ℂ) E E) :
-- imply
  Convex ℝ (numericalRange A) := by
-- proof
  apply InnerProductSpace.ToeplitzHausdorffWanted.toeplitz_hausdorff_general A

/--
[ToeplitzHausdorff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/ToeplitzHausdorff.lean)
-/
@[path]
private lemma toeplitz_hausdorff_is
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (A : ContinuousLinearMap (RingHom.id ℂ) E E) :
-- imply
  Convex ℝ (numericalRange A) := by
-- proof
  apply InnerProductSpace.ToeplitzHausdorffWanted.toeplitz_hausdorff A

-- created on 2026-10-10
