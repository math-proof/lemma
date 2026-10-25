import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Structure.AlgebraicGeometry_CoherentBaseChange

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace CoherentBaseChange


namespace TwoTermComplex

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)

abbrev H0 (A : Type w) [CommRing A] [Algebra R A] : Submodule A (A ⊗[R] G.C0) :=
  LinearMap.ker (G.d.baseChange A)

end TwoTermComplex

end CoherentBaseChange
