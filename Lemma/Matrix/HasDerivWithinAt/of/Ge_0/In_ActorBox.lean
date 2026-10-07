import sympy.stats.frozen_invariant_law
import sympy.Basic
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : EuclideanVec d}
  {t : ℝ}
-- given
  (h₀ : θ ∈ actor_box d r)
  (h₁ : 0 ≤ t)
  (hMix : UniformExponentialMixing r Q)
  (ξ : S → ℝ) :
-- imply
  HasDerivWithinAt (fun s => hMix.semigroup.toFun θ s ξ) (hMix.semigroup.toFun θ t ξ ᵥ* Q θ) (Set.Ici t) t := by
-- proof
  simpa using (hMix.solves_equation θ h₀ ξ).hasDeriv t h₁


-- created on 2026-09-26
