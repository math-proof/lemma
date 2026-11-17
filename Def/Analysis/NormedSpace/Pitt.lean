/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.NormedSpace.Pitt

@[expose] public section

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
