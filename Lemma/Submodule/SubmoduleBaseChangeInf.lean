import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma ker_baseChange_eq {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A] [Module.Flat R A]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    LinearMap.ker (g.baseChange A) = (LinearMap.ker g).baseChange A := by
  have hex : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  have hexA := Module.Flat.lTensor_exact A hex
  rw [LinearMap.exact_iff] at hexA
  ext x
  rw [Submodule.baseChange, LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hx
    have hx' : x ∈ LinearMap.ker (g.lTensor A) := by
      rw [LinearMap.mem_ker, ← LinearMap.baseChange_eq_ltensor]; exact hx
    rw [hexA] at hx'
    obtain ⟨y, hy⟩ := hx'
    exact ⟨y, by rw [LinearMap.baseChange_eq_ltensor]; exact hy⟩
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.comp_ker_subtype, LinearMap.baseChange_zero,
      LinearMap.zero_apply]
/--
[Submodule_baseChange_inf](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_baseChange_inf.lean)
-/
@[path]
private lemma main
    {R : Type*} [Field R] (A : Type*) [CommRing A] [Algebra R A]
    {M : Type*} [AddCommGroup M] [Module R M] (p q : Submodule R M) :
    (p ⊓ q).baseChange A = p.baseChange A ⊓ q.baseChange A := by
  classical
  apply le_antisymm
  · exact le_inf (Submodule.baseChange_mono (A := A) inf_le_left) (Submodule.baseChange_mono (A := A) inf_le_right)
  ·
    let π : M →ₗ[R] (M ⧸ p) × (M ⧸ q) := p.mkQ.prod q.mkQ
    have hπ : LinearMap.ker π = p ⊓ q := by
      rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
    have hp : p.baseChange A = LinearMap.ker (p.mkQ.baseChange A) := by
      rw [ker_baseChange_eq, Submodule.ker_mkQ]
    have hq : q.baseChange A = LinearMap.ker (q.mkQ.baseChange A) := by
      rw [ker_baseChange_eq, Submodule.ker_mkQ]
    rw [← hπ, ← ker_baseChange_eq, hp, hq]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxp, hxq⟩ := hx
    rw [LinearMap.mem_ker] at hxp hxq ⊢
    let e := TensorProduct.prodRight R A A (M ⧸ p) (M ⧸ q)
    have key : ∀ z : A ⊗[R] M, e (π.baseChange A z) = ((p.mkQ.baseChange A) z, (q.mkQ.baseChange A) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]; rfl
      | tmul a m =>
          simp only [LinearMap.baseChange_tmul, π, LinearMap.prod_apply, e]
          exact TensorProduct.prodRight_tmul ..
      | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add, Prod.mk_add_mk]
    apply e.injective
    rw [key, hxp, hxq, map_zero, Prod.mk_zero_zero]

-- created on 2026-10-20
