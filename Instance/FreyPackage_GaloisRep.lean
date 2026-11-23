-- Carved from Lemma/Definitions/Def_FreyPackage_GaloisRep.lean: instance decls only.
module

public import Instance.FLTPrelim_GaloisRep
public import Instance.EllipticCurve_FrobeniusTrace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
@[expose] public section

set_option autoImplicit false

universe r s v


namespace FreyPackage

open WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

noncomputable local instance instDecEqQbarRepresentation : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

end FreyPackage
