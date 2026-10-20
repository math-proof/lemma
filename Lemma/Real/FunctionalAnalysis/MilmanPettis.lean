import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.FunctionalAnalysis.MilmanPettis
open MathlibExt.Analysis.FunctionalAnalysis.MilmanPettisWanted


/--
[milman_pettis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/MilmanPettis.lean)
-/
@[path]
private lemma milman_pettis_eq
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [UniformConvexSpace E] [CompleteSpace E]
  {Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜} :
-- imply
  ∃ x : E, ∀ (f : E →L[𝕜] 𝕜), Φ f = f x := by
-- proof
  apply MathlibExt.Analysis.FunctionalAnalysis.MilmanPettisWanted.milman_pettis Φ


-- created on 2026-10-20
