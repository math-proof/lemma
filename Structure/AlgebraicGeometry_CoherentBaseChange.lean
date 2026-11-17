module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

set_option autoImplicit false

public noncomputable section

open scoped TensorProduct

universe u v w

namespace CoherentBaseChange

structure TwoTermComplex (R : Type u) [CommRing R] where

  C0 : Type v
  [C0_addCommGroup : AddCommGroup C0]
  [C0_module : Module R C0]
  [C0_finite : Module.Finite R C0]
  [C0_free : Module.Free R C0]

  C1 : Type v
  [C1_addCommGroup : AddCommGroup C1]
  [C1_module : Module R C1]
  [C1_finite : Module.Finite R C1]
  [C1_free : Module.Free R C1]

  d : C0 →ₗ[R] C1

attribute [instance] TwoTermComplex.C0_addCommGroup TwoTermComplex.C0_module
  TwoTermComplex.C0_finite TwoTermComplex.C0_free TwoTermComplex.C1_addCommGroup
  TwoTermComplex.C1_module TwoTermComplex.C1_finite TwoTermComplex.C1_free

namespace TwoTermComplex

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)


end TwoTermComplex

end CoherentBaseChange
