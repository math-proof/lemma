module
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theorem.MvPolynomial.CoordRing
public import Def.DrinfeldCurve_CoordRing
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_DrinfeldCurve_CoordRing.lean: instance decls only.

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
