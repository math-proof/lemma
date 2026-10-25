/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.NormedSpace.Pitt


section

namespace FunctionalAnalysis.PittWanted

/-- Head truncation on `ℓ^q`: sum of the first `N` coordinate projections. -/
noncomputable def truncCLM {𝕜 : Type*} [RCLike 𝕜] (q : ENNReal) [Fact (1 ≤ q)]
    (N : ℕ) : lp (fun _ : ℕ => 𝕜) q →L[𝕜] lp (fun _ : ℕ => 𝕜) q :=
  ∑ i ∈ Finset.range N,
    ((lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) q i).comp
      (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) q i))

end FunctionalAnalysis.PittWanted
end
