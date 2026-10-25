-- Carved from Lemma/Definitions/Def_DrinfeldCurve_CoordRing.lean: instance decls only.
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.GaloisField
import Lemma.DrinfeldCurve.CoordRing

set_option autoImplicit false

universe u

noncomputable section

open MvPolynomial

namespace DrinfeldCurve

variable (q : ℕ) (k : Type u) [Field k]

instance instCommRingCoordRing : CommRing (CoordRing q k) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k))

instance instAlgebraCoordRing : Algebra k (CoordRing q k) :=
  inferInstanceAs (Algebra k (MvPolynomial (Fin 2) k ⧸ drinfeldIdeal q k))


end DrinfeldCurve

end
