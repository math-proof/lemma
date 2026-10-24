import Mathlib

set_option autoImplicit false

universe u v w w'

namespace Algebra

def PointDerivations (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] (ev : A →+* k)
    (M : Type w) [AddCommGroup M] [Module k M] : Submodule k (A →ₗ[k] M) where
  carrier := {D | ∀ a b : A, D (a * b) = ev a • D b + ev b • D a}
  add_mem' := by
    intro D D' hD hD' a b
    simp only [LinearMap.add_apply, hD a b, hD' a b, smul_add]
    abel
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro c D hD a b
    simp only [LinearMap.smul_apply, hD a b, smul_add, smul_comm c]

namespace PointDerivations

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] {ev : A →+* k}
  {M : Type w} [AddCommGroup M] [Module k M] {M' : Type w'} [AddCommGroup M'] [Module k M']

theorem mem_iff (D : A →ₗ[k] M) : D ∈ PointDerivations k A ev M ↔ ∀ a b : A, D (a * b) = ev a • D b + ev b • D a :=
  Iff.rfl

theorem apply_mul {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (a b : A) :
    D (a * b) = ev a • D b + ev b • D a := hD a b

theorem apply_one {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, show ev 1 = 1 from map_one ev, one_smul] at h

  have h2 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem apply_algebraMap {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (c : k) : D (algebraMap k A c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, apply_one hD, smul_zero]

theorem ev_smul (hev : ev.comp (algebraMap k A) = RingHom.id k) (c : k) (a : A) : ev (c • a) = c * ev a := by
  rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hev, RingHom.id_apply]

def map (ev : A →+* k) (φ : M →ₗ[k] M') : ↥(PointDerivations k A ev M) →ₗ[k] ↥(PointDerivations k A ev M') where
  toFun D := ⟨φ.comp D.1, fun a b => by simp only [LinearMap.comp_apply, D.2 a b, map_add, map_smul]⟩
  map_add' D D' := by ext a; simp
  map_smul' c D := by ext a; simp

@[simp] theorem map_apply_coe (ev : A →+* k) (φ : M →ₗ[k] M') (D : ↥(PointDerivations k A ev M)) (a : A) :
    (map ev φ D : A →ₗ[k] M') a = φ (D.1 a) := rfl

theorem map_id (ev : A →+* k) (D : ↥(PointDerivations k A ev M)) : map ev (LinearMap.id : M →ₗ[k] M) D = D := by
  ext a; rfl

theorem map_comp {M'' : Type w} [AddCommGroup M''] [Module k M''] (ev : A →+* k) (φ : M →ₗ[k] M') (ψ : M' →ₗ[k] M'')
    (D : ↥(PointDerivations k A ev M)) : map ev (ψ.comp φ) D = map ev ψ (map ev φ D) := by
  ext a; rfl

end PointDerivations

end Algebra
