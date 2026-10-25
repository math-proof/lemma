-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCech.lean: instance decls only.
import Lemma.AlgebraicGeometry.TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Pi
import Lemma.AlgebraicGeometry.OrderedAffineCoverCech

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace


namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

instance instFintypeIdx (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _

instance instDecidableEqIdx (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

end Scheme.OrderedAffineCover


end AlgebraicGeometry

end
