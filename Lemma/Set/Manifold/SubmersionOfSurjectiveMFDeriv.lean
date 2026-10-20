import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.SubmersionOfSurjectiveMFDeriv
open scoped Topology ContDiff
open Manifold
open Manifold.IsSubmersionAt
open MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDerivWanted


/--
[of_surjective_mfderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionOfSurjectiveMFDeriv.lean)
-/
@[path]
private lemma of_surjective_mfderiv_eq
  [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [FiniteDimensional 𝕜 E''] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G}
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N}
  {x : M}
-- given
  (hn : 1 ≤ n)
  (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y)
  (hderiv : Function.Surjective (mfderiv I J f x)) :
-- imply
  IsSubmersionAt I J n f x := by
-- proof
  apply Manifold.IsSubmersionAt.of_surjective_mfderiv hn hfn hderiv

/--
[submersionAt_of_surjective_mfderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionOfSurjectiveMFDeriv.lean)
-/
@[path]
private lemma submersionAt_of_surjective_mfderiv_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [CompleteSpace 𝕜] [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E'']
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N}
  {x : M}
-- given
  (hn : 1 ≤ n)
  (hfn : ∀ᶠ y in 𝓝 x, ContMDiffAt I J n f y)
  (hderiv : Function.Surjective (mfderiv I J f x)) :
-- imply
  IsSubmersionAt I J n f x := by
-- proof
  apply MathlibExt.Geometry.Manifold.SubmersionOfSurjectiveMFDerivWanted.submersionAt_of_surjective_mfderiv hn hfn hderiv


-- created on 2026-10-20
