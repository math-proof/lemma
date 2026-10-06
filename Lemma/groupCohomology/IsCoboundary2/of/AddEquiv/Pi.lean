import Mathlib
import sympy.Basic

open groupCohomology

/--
[groupCohomology_isCoboundary2_of_addEquiv_pi](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_isCoboundary2_of_addEquiv_pi.lean)
-/
@[main]
private lemma main
  {G P P₀ : Type*} [Group G] [AddCommGroup P] [AddCommGroup P₀] [SMul G P]
  {f : G × G → P}
-- given
  (e : P ≃+ (G → P₀))
  (he : ∀ (h : G) (p : P) (x : G), e (h • p) x = e p (h⁻¹ * x))
  (hf : IsCocycle₂ f) :
-- imply
  IsCoboundary₂ f := by
-- proof
  refine ⟨fun g => e.symm (fun y => e (f (y⁻¹, g)) 1), fun g h => ?_⟩
  apply e.injective
  funext y
  simp only [map_add, map_sub, e.apply_symm_apply, Pi.add_apply, Pi.sub_apply, he, mul_inv_rev, inv_inv]

  have hc' : f (y⁻¹ * g, h) - f (y⁻¹, g * h) + f (y⁻¹, g) = y⁻¹ • f (g, h) := by
    rw [sub_add_eq_add_sub, hf y⁻¹ g h, add_sub_cancel_right]
  have := congrArg (fun p => e p 1) hc'
  simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, inv_inv, mul_one] at this
  exact this


-- created on 2026-10-05
