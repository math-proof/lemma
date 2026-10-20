import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.ImmersionOfInjectiveMFDeriv
open scoped Topology ContDiff
open Function Set Manifold
open MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted


/--
[Manifold.IsImmersionAt.of_injective_mfderiv_of_closedComplemented_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean)
-/
@[path]
private lemma Manifold_IsImmersionAt_of_injective_mfderiv_of_closedComplemented_range_eq
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E'] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E' G} [J.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N}
  {x : M}
-- given
  (hn : 1 ≤ n)
  (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y)
  (hderiv : Function.Injective (mfderiv I J f x : E →L[𝕜] E'))
  (hcompl : (mfderiv I J f x : E →L[𝕜] E').range.ClosedComplemented) :
-- imply
  IsImmersionAt I J n f x := by
-- proof
  apply Manifold.IsImmersionAt.of_injective_mfderiv_of_closedComplemented_range hn hfn hderiv hcompl

/--
[immersionAt_of_injective_mfderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean)
-/
@[path]
private lemma immersionAt_of_injective_mfderiv_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [CompleteSpace 𝕜] [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E]
  {E'' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [FiniteDimensional 𝕜 E'']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N}
  {x : M}
-- given
  (hn : 1 ≤ n)
  (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y)
  (hderiv : Function.Injective (mfderiv I J f x)) :
-- imply
  IsImmersionAt I J n f x := by
-- proof
  apply MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted.immersionAt_of_injective_mfderiv hn hfn hderiv


-- created on 2026-10-20
