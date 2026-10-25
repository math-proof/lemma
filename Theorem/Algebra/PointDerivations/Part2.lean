import Mathlib
import Def.Algebra.PointDerivations.Part2
universe u v w w'


namespace Algebra

namespace PointDerivations

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] {ev : A →+* k}
  {M : Type w} [AddCommGroup M] [Module k M] {M' : Type w'} [AddCommGroup M'] [Module k M']

@[simp] theorem map_apply_coe (ev : A →+* k) (φ : M →ₗ[k] M') (D : ↥(PointDerivations k A ev M)) (a : A) :
    (map ev φ D : A →ₗ[k] M') a = φ (D.1 a) :=
  rfl

theorem map_id (ev : A →+* k) (D : ↥(PointDerivations k A ev M)) :
    map ev (LinearMap.id : M →ₗ[k] M) D = D := by
  ext a
  rfl

theorem map_comp {M'' : Type w} [AddCommGroup M''] [Module k M''] (ev : A →+* k)
    (φ : M →ₗ[k] M') (ψ : M' →ₗ[k] M'') (D : ↥(PointDerivations k A ev M)) :
    map ev (ψ.comp φ) D = map ev ψ (map ev φ D) := by
  ext a
  rfl

end PointDerivations
end Algebra
