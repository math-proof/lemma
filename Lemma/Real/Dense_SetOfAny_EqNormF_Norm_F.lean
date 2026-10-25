import Mathlib
import sympy.Basic
import Theorem.Analysis.NormedSpace.BishopPhelps

open FunctionalAnalysis.BanachSpaceWanted

/--
[BishopPhelps](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/BishopPhelps.lean)
-/
@[path]
private lemma bishop_phelps_is
-- given
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
-- imply
  Dense { f : StrongDual 𝕜 E | ∃ x ∈ Metric.closedBall (0 : E) 1, ‖f x‖ = ‖f‖ } := by
-- proof
  apply bishop_phelps

-- created on 2026-10-10
