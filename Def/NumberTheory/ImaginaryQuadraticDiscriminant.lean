/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/

import Def.NumberTheory.DirichletCharacter.Quadratic
import Lemma.Nat.DirichletCharacter.Quadratic
set_option autoImplicit false

/-!
# Imaginary quadratic discriminants

This file specializes the canonical predicate `MetaMathlibExt.IsFundamentalDiscriminant` to
negative discriminants and packages conductor--fundamental-discriminant decompositions.
-/


namespace ImaginaryQuadraticDiscriminant

/-- `D` is an imaginary quadratic discriminant if it is negative and congruent to `0` or `1`
modulo `4`. -/
def IsImaginaryQuadraticDiscriminant (D : Int) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- A fundamental imaginary quadratic discriminant is a negative instance of the canonical
fundamental-discriminant predicate `MetaMathlibExt.IsFundamentalDiscriminant`. -/
def IsFundamentalImaginaryQuadraticDiscriminant (D : Int) : Prop :=
  D < 0 ∧ MetaMathlibExt.IsFundamentalDiscriminant D

/-- The set of imaginary quadratic discriminants. -/
def imaginaryQuadraticDiscriminants : Set Int :=
  {D | IsImaginaryQuadraticDiscriminant D}

/-- The set of fundamental imaginary quadratic discriminants. -/
def fundamentalImaginaryQuadraticDiscriminants : Set Int :=
  {D | IsFundamentalImaginaryQuadraticDiscriminant D}

end ImaginaryQuadraticDiscriminant
