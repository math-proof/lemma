import Mathlib

set_option autoImplicit false

noncomputable section

open scoped Quaternion

namespace QuaternionAlgebra

variable {a b : ℚ}

def qmPeriodMap (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) :
    ℍ[ℚ, a, b] →ₗ[ℤ] (Fin 2 → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => ((ι x).map (algebraMap ℝ ℂ)).mulVec ![(τ : ℂ), 1]
      map_zero' := by simp
      map_add' := fun x y => by simp [Matrix.map_add, Matrix.add_mulVec] }


def qmPeriodLattice (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (τ : UpperHalfPlane) : Submodule ℤ (Fin 2 → ℂ) :=
  Λ.map (qmPeriodMap ι τ)

end QuaternionAlgebra

end
