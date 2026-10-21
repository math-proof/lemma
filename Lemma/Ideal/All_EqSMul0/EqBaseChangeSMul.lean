import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w w'

/--
[LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat.lean)
-/
@[path]
private lemma main
  {R₀ : Type u} [CommRing R₀]
  {R : Type v} [CommRing R] [Algebra R₀ R] [Module.Flat R₀ R]
  {M : Type w} [AddCommGroup M] [Module R₀ M]
  {N : Type w'} [AddCommGroup N] [Module R₀ N]
  (u : M →ₗ[R₀] N)
  (J : Ideal R₀)
  -- given
  (hk : ∀ x : M, u x = 0 → ∀ a ∈ J, a • x = 0)
  (hc : ∀ (y : N), ∀ a ∈ J, ∃ x : M, u x = a • y) :
  -- imply
  (∀ x : TensorProduct R₀ R M, u.baseChange R x = 0 → ∀ a ∈ J.map (algebraMap R₀ R), a • x = 0) ∧
    (∀ y : TensorProduct R₀ R N, ∀ a ∈ J.map (algebraMap R₀ R), ∃ x : TensorProduct R₀ R M, u.baseChange R x = a • y) := by
  -- proof
  set φ := algebraMap R₀ R with hφ
  constructor
  ·
    intro x hx
    have hex : Function.Exact ((LinearMap.ker u).subtype.lTensor R) (u.lTensor R) :=
      Module.Flat.lTensor_exact R (LinearMap.exact_subtype_ker_map u)
    have hx' : u.lTensor R x = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]
      apply hx
    obtain ⟨z, rfl⟩ := (hex x).mp hx'
    have hkill : ∀ j ∈ J, ∀ z : TensorProduct R₀ R (LinearMap.ker u), j • z = 0 := by
      intro j hj z
      induction z using TensorProduct.inductionOn with
      | tmul r k =>
        have : j • k = 0 := Subtype.ext (by simpa using hk k.1 k.2 j hj)
        rw [← TensorProduct.tmul_smul, this, TensorProduct.tmul_zero]
      | add a b ha hb =>
        rw [smul_add, ha, hb, add_zero]
    suffices h : J.map φ ≤ Ideal.torsionOf R _ ((LinearMap.ker u).subtype.lTensor R z) by
      intro a ha
      apply (Ideal.mem_torsionOf_iff _ _).mp (h ha)
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, algebraMap_smul, ← LinearMap.map_smul, hkill j hj z, map_zero]
  ·
    intro y a ha
    suffices h : (J.map φ) • (⊤ : Submodule R (TensorProduct R₀ R N)) ≤ LinearMap.range (u.baseChange R) by
      apply h (Submodule.smul_mem_smul ha (Submodule.mem_top : y ∈ ⊤))
    have h1 : ((J.map φ) • (⊤ : Submodule R (TensorProduct R₀ R N))).restrictScalars R₀ ≤
        (LinearMap.range (u.baseChange R)).restrictScalars R₀ := by
      rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top, Submodule.smul_le]
      rintro j hj y -
      show j • y ∈ LinearMap.range (u.baseChange R)
      induction y using TensorProduct.inductionOn with
      | tmul r n =>
        obtain ⟨x, hx⟩ := hc n j hj
        refine ⟨TensorProduct.tmul R₀ r x, ?_⟩
        rw [LinearMap.baseChange_tmul, hx, TensorProduct.tmul_smul]
      | add a b ha hb =>
        rw [smul_add]
        apply Submodule.add_mem _ ha hb
    intro v hv
    apply h1 hv


-- created on 2026-10-20
