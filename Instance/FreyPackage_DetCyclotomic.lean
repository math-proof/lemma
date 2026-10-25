-- Carved from Lemma/Definitions/Def_FreyPackage_DetCyclotomic.lean: instance decls only.
import Instance.FreyPackage_GaloisRep
import Def.FLTPrelim_Ramification
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.LinearAlgebra.Determinant
import Def.ExtCitation_AdmissibleExtension

set_option autoImplicit false

universe r s v


namespace FreyPackage

open WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

noncomputable local instance instDecEqQbarDetCyclotomic : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

variable (P : FreyPackage)

end FreyPackage
