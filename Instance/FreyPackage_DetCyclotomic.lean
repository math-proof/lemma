-- Carved from Lemma/Definitions/Def_FreyPackage_DetCyclotomic.lean: instance decls only.
module

public import Instance.FreyPackage_GaloisRep
public import Def.FLTPrelim_Ramification
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.LinearAlgebra.Determinant
public import Def.ExtCitation_AdmissibleExtension
@[expose] public section

set_option autoImplicit false

universe r s v


namespace FreyPackage

open WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

noncomputable local instance instDecEqQbarDetCyclotomic : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

variable (P : FreyPackage)

end FreyPackage
