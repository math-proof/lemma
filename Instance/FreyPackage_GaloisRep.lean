-- Carved from Lemma/Definitions/Def_FreyPackage_GaloisRep.lean: instance decls only.
import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Instance.EllipticCurve_FrobeniusTrace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option autoImplicit false

universe r s v


namespace FreyPackage

open WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

noncomputable local instance instDecEqQbarRepresentation : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

end FreyPackage
