import Mathlib
import Theorem.Algebra.PointDerivations
universe u v w w'


namespace Algebra

namespace PointDerivations

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] {ev : A →+* k}
  {M : Type w} [AddCommGroup M] [Module k M] {M' : Type w'} [AddCommGroup M'] [Module k M']

def map (ev : A →+* k) (φ : M →ₗ[k] M') :
    ↥(PointDerivations k A ev M) →ₗ[k] ↥(PointDerivations k A ev M') where
  toFun D := ⟨φ.comp D.1, fun a b => by simp only [LinearMap.comp_apply, D.2 a b, map_add, map_smul]⟩
  map_add' D D' := by
    ext a
    simp
  map_smul' c D := by
    ext a
    simp

end PointDerivations
end Algebra
