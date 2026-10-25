-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_ShimuraCurve.lean: instance decls only.
import Lemma.QuaternionAlgebra.EichlerOrder
import Lemma.QuaternionAlgebra.ReducedNorm
import Def.ModularCurve_UniformizedHeckeCurve
import Instance.AlgebraicCurve_BaseChangeGalois
import Instance.AlgebraicCurve_IsCurveOver
import Structure.CerednikDrinfeld_TwoPlaceTorsionDatum
import Instance.Compat_Mathlib430
import Lemma.CerednikDrinfeld.ShimuraCurve

set_option autoImplicit false

noncomputable section

open scoped Quaternion TensorProduct MatrixGroups
open IsDedekindDomain NumberField AlgebraicCurve


namespace CerednikDrinfeld

open QuaternionAlgebra ModularCurve

variable {a b : ℚ}


namespace ShimuraCurveModel

variable {R : Submodule ℤ ℍ[ℚ, a, b]} {ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ}

instance instFiniteTors (M : ShimuraCurveModel R ι 𝒮) (p : ℕ) [Fact p.Prime] : Finite (M.Tors p) :=
  M.finite_torsion p (Fact.out : p.Prime).pos

end ShimuraCurveModel

end CerednikDrinfeld

end
