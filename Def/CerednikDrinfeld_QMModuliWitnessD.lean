import Def.CerednikDrinfeld_QMModuli
import Structure.CerednikDrinfeld_QMModuliWitnessD

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld

open CerednikDrinfeld.QM

variable {a b : ℚ}


def ShimuraCurveModel.IsModuliModelD {R₀ : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
    {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (M : ShimuraCurveModel R₀ ι 𝒮) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N q q' D : ℕ) : Prop :=
  Nonempty (M.ModuliWitnessD Λ N q q' D)

end CerednikDrinfeld

end
