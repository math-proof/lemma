import Mathlib
import Structure.TateCurve_XMultDistinctRouteB
import Lemma.WeierstrassCurve.TateFiltrationPrep
import Structure.TateCurve_KeystoneVocab
import Theorems.Thm_TateCurve_symAddHyps_unconditional
import Theorems.Thm_TateCurve_diffHyp_unconditional
import Theorems.Thm_TateCurve_eq_zero_or_eq_tateParam_unconditional

set_option linter.unusedSectionVars false
set_option autoImplicit false

universe u

namespace WeierstrassCurve
variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

abbrev n_torsionGen (n : ℕ) : Type u := Submodule.torsionBy ℤ W.toAffine.Point n
end WeierstrassCurve

namespace WeierstrassCurve.Affine
variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

end WeierstrassCurve.Affine

open WeierstrassCurve.Affine

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v w ζ t : K} {p : ℕ}

section LatticeHelpers

end LatticeHelpers

section TateParameters

variable {p : ℕ}

end TateParameters

end TateCurve

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K] [IsAlgClosed K]
variable {q ζ t : K} {p : ℕ}

section UnconditionalCascade

end UnconditionalCascade

section Parametrization

end Parametrization

section GroupStructure

end GroupStructure

section GaloisAction

end GaloisAction

end TateCurve
