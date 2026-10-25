import Def.QuaternionAlgebra_EichlerOrder
import Def.QuaternionAlgebra_ReducedNorm
import Structure.ModularCurve_UniformizedHeckeCurve
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Instance.AlgebraicCurve_IsCurveOver
import Structure.CerednikDrinfeld_TwoPlaceTorsionDatum
import Instance.Compat_Mathlib430

set_option autoImplicit false

noncomputable section

open scoped Quaternion TensorProduct MatrixGroups
open IsDedekindDomain NumberField AlgebraicCurve

namespace QuaternionAlgebra

variable (a b : ℚ)

end QuaternionAlgebra

namespace CerednikDrinfeld

open QuaternionAlgebra ModularCurve

variable {a b : ℚ}


namespace ShimuraCurveModel

variable {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}
  {𝒮 : ℕ → Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

abbrev J (M : ShimuraCurveModel R ι 𝒮) : Type := Pic0 (AlgebraicClosure ℚ) M.Fbar

abbrev Tors (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) : Type := ↥(Pic0.torsion (AlgebraicClosure ℚ) M.Fbar p)

end ShimuraCurveModel

end CerednikDrinfeld

end
