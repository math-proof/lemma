import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Algebra.PointDerivations.Part2
import Def.Algebra_PointDerivations
open Algebra.PointDerivations

/--
[Algebra_PointDerivations_finite_and_finrank_eq_mul_of_surjective_of_ker](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_PointDerivations_finite_and_finrank_eq_mul_of_surjective_of_ker.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A]
  {Ω : Type w} [AddCommGroup Ω] [Module k Ω] [Module.Finite k Ω]
  {M : Type w'} [AddCommGroup M] [Module k M] [Module.Finite k M]
  {ev : A →+* k}
  {π : ↥((RingHom.ker ev).restrictScalars k) →ₗ[k] Ω}
-- given
  (hev : ev.comp (algebraMap k A) = RingHom.id k)
  (hπ : Function.Surjective π)
  (hπker : ∀ x : ↥((RingHom.ker ev).restrictScalars k), π x = 0 ↔ (x : A) ∈ (RingHom.ker ev) ^ 2) :
-- imply
  Module.Finite k ↥(Algebra.PointDerivations k A ev M) ∧
    Module.finrank k ↥(Algebra.PointDerivations k A ev M) = Module.finrank k Ω * Module.finrank k M := by
-- proof
  have hevc : ∀ c : k, ev (algebraMap k A c) = c := fun c => RingHom.congr_fun hev c
  let evₗ : A →ₗ[k] k := {
    toFun := ev
    map_add' := ev.map_add
    map_smul' := by
      intro c a
      rw [ev_smul hev, RingHom.id_apply, smul_eq_mul]
  }
  let ρ' : A →ₗ[k] A := LinearMap.id - (Algebra.linearMap k A).comp evₗ
  have hρ' : ∀ a : A, ρ' a ∈ (RingHom.ker ev).restrictScalars k := fun a => by
    show a - algebraMap k A (ev a) ∈ RingHom.ker ev
    rw [RingHom.mem_ker, map_sub, hevc, sub_self]
  let ρ : A →ₗ[k] ↥((RingHom.ker ev).restrictScalars k) := ρ'.codRestrict _ hρ'
  have hρ : ∀ a : A, (ρ a : A) = a - algebraMap k A (ev a) := fun a => rfl
  have hρmem : ∀ m : ↥((RingHom.ker ev).restrictScalars k), ρ (m : A) = m := fun m => by
    apply Subtype.ext
    have hm : ev (m : A) = 0 := m.2
    rw [hρ, hm, map_zero, sub_zero]
  have hD2 : ∀ (D : ↥(Algebra.PointDerivations k A ev M)) (y : A),
      y ∈ RingHom.ker ev ^ 2 → (D : A →ₗ[k] M) y = 0 := by
    intro D y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy (fun m hm n hn => ?_) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
    rw [D.2 m n, show ev m = 0 from hm, show ev n = 0 from hn, zero_smul, zero_smul, add_zero]
  have hkey : ∀ a b : A, π (ρ (a * b)) = ev a • π (ρ b) + ev b • π (ρ a) := by
    intro a b
    have hX : ((ρ (a * b) - ev a • ρ b - ev b • ρ a : ↥((RingHom.ker ev).restrictScalars k)) : A) ∈
      RingHom.ker ev ^ 2 := by
      have hcalc : ((ρ (a * b) - ev a • ρ b - ev b • ρ a : ↥((RingHom.ker ev).restrictScalars k)) : A) =
        (ρ a : A) * (ρ b : A) := by
        simp [hρ, Algebra.smul_def, map_mul]
        ring
      rw [hcalc, pow_two]
      apply Ideal.mul_mem_mul (ρ a).2 (ρ b).2
    have h0 := (hπker _).mpr hX
    rw [map_sub, map_sub, map_smul, map_smul] at h0
    rw [← sub_eq_zero, ← h0]
    abel
  have hΨmem : ∀ (φ : Ω →ₗ[k] M) (a b : A),
      (φ.comp (π.comp ρ)) (a * b) =
        ev a • (φ.comp (π.comp ρ)) b + ev b • (φ.comp (π.comp ρ)) a := by
    intro φ a b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hkey, map_add, map_smul, map_smul]
    simp [LinearMap.comp_apply]
  let Ψ : (Ω →ₗ[k] M) →ₗ[k] ↥(Algebra.PointDerivations k A ev M) := {
    toFun := fun φ => ⟨φ.comp (π.comp ρ), hΨmem φ⟩
    map_add' := by
      intro φ φ'
      apply Subtype.ext
      ext a
      rfl
    map_smul' := by
      intro c φ
      apply Subtype.ext
      ext a
      rfl
  }
  have hΨ : ∀ (φ : Ω →ₗ[k] M) (a : A), (Ψ φ : A →ₗ[k] M) a = φ (π (ρ a)) := fun φ a => rfl
  have hinj : Function.Injective Ψ := by
    intro φ φ' hφ
    ext ω
    obtain ⟨m, rfl⟩ := hπ ω
    have : (Ψ φ : A →ₗ[k] M) (m : A) = (Ψ φ' : A →ₗ[k] M) (m : A) := by
      rw [hφ]
    rw [hΨ, hΨ, hρmem] at this
    apply this
  have hsurj : Function.Surjective Ψ := by
    intro D
    obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.mpr hπ)
    refine ⟨(D : A →ₗ[k] M).comp (((RingHom.ker ev).restrictScalars k).subtype.comp σ), ?_⟩
    apply Subtype.ext
    ext a
    rw [hΨ]
    simp [LinearMap.comp_apply, Submodule.subtype_apply]
    have h1 : (D : A →ₗ[k] M) ((σ (π (ρ a)) - ρ a : ↥((RingHom.ker ev).restrictScalars k)) : A) = 0 := by
      refine hD2 D _ ((hπker _).mp ?_)
      have hc := LinearMap.congr_fun hσ (π (ρ a))
      rw [LinearMap.comp_apply, LinearMap.id_apply] at hc
      rw [map_sub, hc, sub_self]
    rw [Submodule.coe_sub, map_sub, sub_eq_zero] at h1
    rw [h1, hρ, map_sub, apply_algebraMap D.2, sub_zero]
  let e : (Ω →ₗ[k] M) ≃ₗ[k] ↥(Algebra.PointDerivations k A ev M) := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_linearMap]

-- created on 2026-10-16
