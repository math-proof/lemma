import Mathlib
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

end Algebra
