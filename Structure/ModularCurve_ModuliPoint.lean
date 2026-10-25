import Mathlib
import Def.WeierstrassCurve_VariableChangePointEquiv
import Lemma.WeierstrassCurve.RatPointHom

noncomputable section

namespace ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine

section Pairs

variable (N : ℕ) (L : Type*) [Field L] [DecidableEq L]

structure Gamma0Pair where

  toCurve : WeierstrassCurve L

  isElliptic : toCurve.IsElliptic

  gen : toCurve.toAffine.Point

  addOrderOf_gen : addOrderOf gen = N

attribute [instance] Gamma0Pair.isElliptic

variable {N L}


variable (N L) in


end Pairs

section HEqToolbox

variable {K : Type*} [Field K]


end HEqToolbox

section Map

variable {L L' : Type} [Field L] [Field L']
variable [DecidableEq L] [DecidableEq L']


variable {N : ℕ}


end Map

end ModularCurve

end
