import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.TangentCone.Real
import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.UniformExponentialMixing.HasDerivWithinAt.of.Ge_0.In_ActorBox
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
  hMix.semigroup.toFun θ t (ξ ᵥ* Q θ) = hMix.semigroup.toFun θ t ξ ᵥ* Q θ := by
-- proof
  let T := hMix.semigroup.toFun θ
  have hF : HasDerivWithinAt (fun s => T t (T s ξ)) (T t (ξ ᵥ* Q θ)) (Set.Ici 0) 0 := by
    have h := UniformExponentialMixing.HasDerivWithinAt.of.Ge_0.In_ActorBox h₀ le_rfl hMix ξ
    rw [hMix.semigroup.map_zero' θ, ContinuousLinearMap.id_apply] at h
    exact (T t).hasFDerivAt.comp_hasDerivWithinAt 0 h
  have hG : HasDerivWithinAt (fun s => T (t + s) ξ) (T t ξ ᵥ* Q θ) (Set.Ici 0) 0 := by
    have hadd : HasDerivWithinAt (fun s : ℝ => t + s) 1 (Set.Ici 0) 0 := ((hasDerivAt_id 0).const_add t).hasDerivWithinAt
    have hmaps : Set.MapsTo (fun s : ℝ => t + s) (Set.Ici 0) (Set.Ici t) := fun s hs => by
      simp only [Set.mem_Ici] at hs ⊢
      linarith
    have h := (UniformExponentialMixing.HasDerivWithinAt.of.Ge_0.In_ActorBox h₀ h₁ hMix ξ).scomp_of_eq 0 hadd hmaps (by simp)
    simp only [one_smul] at h
    exact h
  have hG' : HasDerivWithinAt (fun s => T (t + s) ξ) (T t (ξ ᵥ* Q θ)) (Set.Ici 0) 0 := by
    refine hF.congr_of_mem (fun s hs => ?_) Set.self_mem_Ici
    show hMix.semigroup.toFun θ (t + s) ξ = hMix.semigroup.toFun θ t (hMix.semigroup.toFun θ s ξ)
    rw [hMix.semigroup.map_add' θ t s h₁ hs]
    rfl
  exact ((uniqueDiffOn_Ici (0 : ℝ)) 0 Set.self_mem_Ici).eq_deriv _ hG' hG


-- created on 2026-09-26
