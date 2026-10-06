import Mathlib
import sympy.Basic

open groupCohomology

/--
[groupCohomology_isCoboundary1_of_addEquiv_pi](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_isCoboundary1_of_addEquiv_pi.lean)
-/
@[main]
private lemma main
  {G P P₀ : Type*} [Group G] [AddCommGroup P] [AddCommGroup P₀] [SMul G P]
  {f : G → P}
-- given
  (e : P ≃+ (G → P₀))
  (he : ∀ (h : G) (p : P) (x : G), e (h • p) x = e p (h⁻¹ * x))
  (hf : IsCocycle₁ f) :
-- imply
  IsCoboundary₁ f := by
-- proof
  refine ⟨e.symm (fun x => e (f x⁻¹) 1), fun g => ?_⟩
  apply e.injective
  funext x
  rw [map_sub, e.apply_symm_apply, Pi.sub_apply, he, e.apply_symm_apply, mul_inv_rev, inv_inv]

  rw [hf x⁻¹ g, map_add, Pi.add_apply, he, inv_inv, mul_one, add_sub_cancel_right]


-- created on 2026-10-05
