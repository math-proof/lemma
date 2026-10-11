import Mathlib
import sympy.Basic
import sympy.calculus.functional_analysis.RosenthalL1

open FunctionalAnalysis.RosenthalL1Wanted

/--
[RosenthalL1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/RosenthalL1.lean)
-/
@[path]
private lemma rosenthal_l1_eq
-- given
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (x : ℕ → E)
  (hx : Bornology.IsBounded (Set.range x)) :
-- imply
  ∃ (φ : ℕ → ℕ) (_ : StrictMono φ),
    (∀ (f : E →L[𝕜] 𝕜) (ε : ℝ), 0 < ε →
      ∃ N, ∀ m n, N ≤ m → N ≤ n → ‖f (x (φ m)) - f (x (φ n))‖ < ε) ∨
    HasUniformL1LowerBound (𝕜 := 𝕜) (x ∘ φ) := by
-- proof
  apply rosenthal_l1 x hx

-- created on 2026-10-10
