import Mathlib
import Structure.TateCurve_XMultStructure
import Def.TateCurve_TateParameter
import Lemma.WeierstrassCurve.AddFormula
import Def.NetPairing_Basic
import Theorems.Thm_TateCurve_equation_pointX_pointY
import Theorems.Thm_TateCurve_pointX_inv
import Theorems.Thm_TateCurve_pointX_zpow_mul

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

end WeierstrassCurve.Affine

set_option linter.unusedSectionVars false

open WeierstrassCurve.Affine
open Polynomial

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u : K}

structure SymAddHyps (q : K) : Prop where

  sum : ∀ u v : K, AddParams q u v →
    (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      symSumNum q (pointX q u) (pointX q v)

  prod : ∀ u v : K, AddParams q u v →
    pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
      symProdNum q (pointX q u) (pointX q v)

  dbl : ∀ u : K, u ≠ 0 → OffLattice q u → OffLattice q (u ^ 2) →
    pointX q (u ^ 2) * ((curve q).Ψ₂Sq).eval (pointX q u) =
      ((curve q).Φ 2).eval (pointX q u)

end TateCurve
