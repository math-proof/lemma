import Mathlib.MeasureTheory.Integral.ExpDecay
import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.Real.Norm.le.Sum_Abs
open Filter MeasureTheory


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : EuclideanVec d}
  {ξ : S → ℝ}
-- given
  (h₀ : θ ∈ actor_box d r)
  (h₁ : ∑ i, ξ i = 0)
  (hMix : UniformExponentialMixing r Q) :
-- imply
  IntegrableOn (fun t => hMix.semigroup.toFun θ t ξ) (Set.Ioi 0) := by
-- proof
  have hbound : IntegrableOn (fun t => hMix.cMix * (∑ i, |ξ i|) * Real.exp (-hMix.γ * t)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hMix.γ_pos).const_mul _
  refine hbound.mono' (hMix.solves_equation θ h₀ ξ).cont.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
  calc
    _ ≤ _ := Real.Norm.le.Sum_Abs _
    _ ≤ _ := hMix.mixing θ h₀ ξ h₁ t (le_of_lt ht)
    _ = _ := by ring


-- created on 2026-09-26
