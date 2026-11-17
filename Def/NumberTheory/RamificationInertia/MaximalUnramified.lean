/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/MaximalUnramified.lean -/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.Algebra.Algebra.RestrictScalars

@[expose] public section

/-! Finite formally unramified intermediate fields relative to a base ring, their
supremum, its universal property, and automorphism invariance. -/


namespace IntermediateField

variable {A K L : Type*} [CommRing A] [Field K] [Field L]

variable [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- An intermediate field is finite unramified relative to `A` if it is finite over `K` and its
`A`-integral closure is formally unramified over `A`. -/
def IsFiniteUnramified (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    (E : IntermediateField K L) : Prop :=
  FiniteDimensional K E ∧ Algebra.FormallyUnramified A (integralClosure A E)

/-- The maximal unramified subextension, defined as the
supremum of all finite unramified intermediate fields. The supremum need not itself be finite or
formally unramified. -/
noncomputable def maximalUnramifiedSubextension (A K L : Type*) [CommRing A]
    [Field K] [Field L] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] : IntermediateField K L :=
  ⨆ (E : IntermediateField K L) (_ : IsFiniteUnramified A E), E

end IntermediateField
