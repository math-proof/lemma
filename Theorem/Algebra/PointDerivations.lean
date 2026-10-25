import Mathlib
import Def.Algebra.PointDerivations
universe u v w w'


namespace Algebra

namespace PointDerivations

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] {ev : A →+* k}
  {M : Type w} [AddCommGroup M] [Module k M] {M' : Type w'} [AddCommGroup M'] [Module k M']

theorem mem_iff (D : A →ₗ[k] M) :
    D ∈ PointDerivations k A ev M ↔ ∀ a b : A, D (a * b) = ev a • D b + ev b • D a :=
  Iff.rfl

theorem apply_mul {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (a b : A) :
    D (a * b) = ev a • D b + ev b • D a :=
  hD a b

theorem apply_one {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) : D 1 = 0 := by
  have h := hD 1 1
  rw [mul_one, show ev 1 = 1 from map_one ev, one_smul] at h
  have h2 : D 1 + D 1 = D 1 + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

theorem apply_algebraMap {D : A →ₗ[k] M} (hD : D ∈ PointDerivations k A ev M) (c : k) :
    D (algebraMap k A c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, apply_one hD, smul_zero]

theorem ev_smul (hev : ev.comp (algebraMap k A) = RingHom.id k) (c : k) (a : A) :
    ev (c • a) = c * ev a := by
  rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hev, RingHom.id_apply]

end PointDerivations
end Algebra
