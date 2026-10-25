import Mathlib
import Def.QuaternionAlgebra_QMPeriodLattice

set_option autoImplicit false

noncomputable section

open scoped Quaternion

namespace QuaternionAlgebra

variable {a b : ℚ}


@[simp]
theorem qmPeriodMap_apply (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane)
    (x : ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ x = ((ι x).map (algebraMap ℝ ℂ)).mulVec ![(τ : ℂ), 1] :=
  rfl


theorem mem_qmPeriodLattice_iff (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (τ : UpperHalfPlane) (v : Fin 2 → ℂ) :
    v ∈ qmPeriodLattice ι Λ τ ↔ ∃ x ∈ Λ, qmPeriodMap ι τ x = v :=
  Submodule.mem_map

end QuaternionAlgebra

end
