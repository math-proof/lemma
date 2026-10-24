import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[LinearMap_finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso.lean)
-/
@[path]
private lemma main
  {A : Type u} [Field A]
  (K : ℕ → Type v) [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)] [∀ i, Module.Finite A (K i)]
  (δ : ∀ i, K i →ₗ[A] K (i + 1))
  (C : ℕ → Type v) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)]
  (d : ∀ i, C i →ₗ[A] C (i + 1))
  (φ : ∀ i, K i →ₗ[A] C i)
  (hφ : ∀ i, LinearMap.comp (d i) (φ i) = LinearMap.comp (φ (i + 1)) (δ i))
  (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
  (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
  (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) → x ∈ LinearMap.range (δ i))
  (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 → ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i)) :
  -- imply
  Module.finrank A ↥(LinearMap.ker (d 0)) = Module.finrank A ↥(LinearMap.ker (δ 0)) ∧ ∀ (i : ℕ) (H : Type v) [AddCommGroup H] [Module A H] (ψ : ↥(LinearMap.ker (d (i + 1))) →ₗ[A] H), Function.Surjective ψ → LinearMap.ker ψ = (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype → Module.finrank A H + Module.finrank A ↥((LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) = Module.finrank A ↥(LinearMap.ker (δ (i + 1))) := by
  -- proof
  classical
  have hφ' : ∀ (i : ℕ) (x : K i), d i (φ i x) = φ (i + 1) (δ i x) := fun i x => congrArg (fun f => f x) (hφ i) |>.trans rfl
  refine ⟨?_, ?_⟩
  ·
    let e0 : ↥(LinearMap.ker (δ 0)) →ₗ[A] ↥(LinearMap.ker (d 0)) := ⟨⟨fun x => ⟨φ 0 x.1, by rw [LinearMap.mem_ker, hφ' 0, LinearMap.mem_ker.mp x.2, map_zero]⟩, fun x y => Subtype.ext (by simp)⟩, fun a x => Subtype.ext (by simp)⟩
    have hinj0 : Function.Injective e0 := by
      intro x y hxy
      apply Subtype.ext
      have h := congrArg Subtype.val hxy
      simp only [e0, LinearMap.coe_mk, AddHom.coe_mk] at h
      have : x.1 - y.1 = 0 := h0inj (x.1 - y.1) (by rw [map_sub, LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2, sub_zero]) (by rw [map_sub, h, sub_self])
      refine sub_eq_zero.mp this
    have hsurj0 : Function.Surjective e0 := by
      intro y
      obtain ⟨x, hx, hxy⟩ := h0surj y.1 (LinearMap.mem_ker.mp y.2)
      exact ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, Subtype.ext hxy⟩
    refine (LinearEquiv.ofBijective e0 ⟨hinj0, hsurj0⟩).finrank_eq.symm
  ·
    intro i H _ _ ψ hψ hker
    let r : ↥(LinearMap.ker (δ (i + 1))) →ₗ[A] ↥(LinearMap.ker (d (i + 1))) := ⟨⟨fun x => ⟨φ (i + 1) x.1, by rw [LinearMap.mem_ker, hφ' (i + 1), LinearMap.mem_ker.mp x.2, map_zero]⟩, fun x y => Subtype.ext (by simp)⟩, fun a x => Subtype.ext (by simp)⟩
    let Φ : ↥(LinearMap.ker (δ (i + 1))) →ₗ[A] H := LinearMap.comp ψ r
    have hΦsurj : Function.Surjective Φ := by
      intro h
      obtain ⟨y, rfl⟩ := hψ h
      obtain ⟨x, hx, hxy⟩ := hsurj i y.1 (LinearMap.mem_ker.mp y.2)
      refine ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, ?_⟩
      show ψ (r ⟨x, _⟩) = ψ y
      rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, hker, Submodule.mem_comap]
      apply hxy
    have hΦker : LinearMap.ker Φ = (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype := by
      ext x
      rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
      show ψ (r x) = 0 ↔ x.1 ∈ LinearMap.range (δ i)
      rw [← LinearMap.mem_ker, hker, Submodule.mem_comap, Submodule.coe_subtype]
      show φ (i + 1) x.1 ∈ LinearMap.range (d i) ↔ x.1 ∈ LinearMap.range (δ i)
      constructor
      ·
        apply hinj i x.1 (LinearMap.mem_ker.mp x.2)
      ·
        rintro ⟨z, hz⟩
        exact ⟨φ i z, by rw [hφ' i, hz]⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    rw [LinearMap.range_eq_top.mpr hΦsurj, finrank_top, hΦker] at hrn
    apply hrn


-- created on 2026-10-20
