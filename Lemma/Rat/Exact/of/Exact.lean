import Mathlib
import sympy.Basic


/--
[LinearMap_exact_dualMap_of_exact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_exact_dualMap_of_exact.lean)
-/
@[main]
private lemma main
  {K V₁ V₂ V₃ : Type*} [Field K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]
  {f : V₁ →ₗ[K] V₂}
  {g : V₂ →ₗ[K] V₃}
-- given
  (h : Function.Exact f g) :
-- imply
  Function.Exact g.dualMap f.dualMap := by
-- proof
  rw [LinearMap.exact_iff] at h ⊢
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, h]
  ext ψ
  simp only [LinearMap.mem_ker, Submodule.mem_dualAnnihilator, LinearMap.mem_range]
  constructor
  · rintro hψ _ ⟨y, rfl⟩
    exact congrArg (fun χ : Module.Dual K V₁ => χ y) hψ
  · intro hψ
    ext y
    exact hψ _ ⟨y, rfl⟩


-- created on 2026-10-05
