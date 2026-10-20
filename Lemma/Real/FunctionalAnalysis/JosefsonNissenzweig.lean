import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.FunctionalAnalysis.JosefsonNissenzweig
open MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted


/--
[josefson_nissenzweig](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean)
-/
@[path]
private lemma josefson_nissenzweig_eq
  [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
-- given
  (hInf : ¬ FiniteDimensional 𝕜 E) :
-- imply
  ∃ (φ : ℕ → StrongDual 𝕜 E), (∀ n, ‖φ n‖ = 1) ∧
    ∀ x : E, Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
-- proof
  apply MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted.josefson_nissenzweig hInf


-- created on 2026-10-20
