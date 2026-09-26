import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import sympy.dynamics.actor_critic
import sympy.Basic
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {d : ℕ}
  {δ : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : ℝ → EuclideanVec d}
  {μ : ℝ → S → ℝ}
  {a : ℝ}
-- given
  (h₀ : ForwardSolvesStateEquation δ Q θ μ)
  (h₁ : 0 ≤ a) :
-- imply
  ForwardSolvesStateEquation δ Q (fun t => θ (a + t)) (fun t => μ (a + t)) := by
-- proof
  refine ⟨h₀.cont.comp (continuous_const.add continuous_id), fun t ht => ?_⟩
  have hs : HasDerivWithinAt (fun s : ℝ => a + s) 1 (Set.Ici t) t := ((hasDerivAt_id t).const_add a).hasDerivWithinAt
  have hm : Set.MapsTo (fun s : ℝ => a + s) (Set.Ici t) (Set.Ici (a + t)) := fun s hs => by
    simp only [Set.mem_Ici] at hs ⊢
    linarith
  have h := (h₀.hasDeriv (a + t) (add_nonneg h₁ ht)).scomp t hs hm
  simp only [one_smul] at h
  exact h


-- created on 2026-09-26
