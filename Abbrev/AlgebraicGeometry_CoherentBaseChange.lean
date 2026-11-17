module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Structure.AlgebraicGeometry_CoherentBaseChange

set_option autoImplicit false

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace CoherentBaseChange


namespace TwoTermComplex

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)

abbrev H0 (A : Type w) [CommRing A] [Algebra R A] : Submodule A (A ⊗[R] G.C0) :=
  LinearMap.ker (G.d.baseChange A)

end TwoTermComplex

end CoherentBaseChange
