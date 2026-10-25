import Mathlib
import Structure.TateCurve_XMultAlignment
import Theorems.Thm_TateCurve_pointY_inv
import Theorems.Thm_TateCurve_pointY_zpow_mul
import Theorems.Thm_TateCurve_pointX_qExpansion
import Def.TateCurve_XMultDistinctRouteB

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WeierstrassCurve

section Bezout

variable {F : Type*} [Field F] (W : WeierstrassCurve F)


end Bezout

end WeierstrassCurve

namespace TateCurve

section AnnulusTranslateExtra
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K}


end AnnulusTranslateExtra

end TateCurve

set_option linter.unusedSectionVars false

open WeierstrassCurve.Affine
open Polynomial
open IsUltrametricDist

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v : K}

section Factorization


end Factorization

section Fiber


end Fiber

section TwoTorsion


end TwoTorsion

section Consumers


end Consumers

end TateCurve

open Polynomial
open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u : K}


section AuxiliarySupply

private structure DiamondAux (q u w : K) : Prop where
  ne_zero : w ≠ 0
  nnnorm_eq : ‖w‖₊ = 1
  offLattice : OffLattice q w
  offLattice_sq : OffLattice q (w ^ 2)
  offLattice_mul : OffLattice q (u * w)
  offLattice_div : OffLattice q (u * w⁻¹)


end AuxiliarySupply


end TateCurve

set_option linter.unusedSectionVars false

open Polynomial
open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v : K}


section PerPair


end PerPair

section Forall


end Forall

end TateCurve
