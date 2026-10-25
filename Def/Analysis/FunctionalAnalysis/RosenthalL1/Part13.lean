/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Instance.Analysis.FunctionalAnalysis.RosenthalL1
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

noncomputable def rosenthalDualBallStrong
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (g : RosenthalDualBall 𝕜 E) : StrongDual 𝕜 E :=
  WeakDual.toStrongDual g.1

noncomputable def rosenthalDualEval
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (n : ℕ) (g : RosenthalDualBall 𝕜 E) : 𝕜 :=
  g.1 (x n)

/-- `y : ℕ → E` has a uniform `ℓ¹` lower bound when some `c > 0` satisfies
`‖∑ i, a i • y i‖ ≥ c * ∑ i, ‖a i‖` for every finitely supported `a : ℕ →₀ 𝕜`. -/
def HasUniformL1LowerBound {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (y : ℕ → E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (a : ℕ →₀ 𝕜),
    ‖∑ i ∈ a.support, a i • y i‖ ≥ c * ∑ i ∈ a.support, ‖a i‖

end MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted
