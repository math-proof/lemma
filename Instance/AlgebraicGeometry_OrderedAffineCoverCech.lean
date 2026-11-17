-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCech.lean: instance decls only.

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Pi
public import Structure.AlgebraicGeometry_OrderedAffineCoverCech

@[expose] public section

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
