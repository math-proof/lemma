/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/


import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part24
import Lemma.Real.FunctionalAnalysis.JosefsonNissenzweig
open MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted


-- The theorem supplies a normalized weak-star-null sequence from infinite dimensionality.
example {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] (hInf : ¬ FiniteDimensional 𝕜 E) :
    ∃ (φ : ℕ → StrongDual 𝕜 E), (∀ n, ‖φ n‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
  exact josefson_nissenzweig hInf

