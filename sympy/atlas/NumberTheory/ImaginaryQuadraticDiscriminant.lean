/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/

import sympy.atlas.NumberTheory.DirichletCharacter.Quadratic
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

/-- A decomposition `D = u ^ 2 * D_K` into a positive conductor and a fundamental imaginary
quadratic discriminant. -/
structure ImaginaryQuadraticDiscriminantDecomposition (D : Int) where
  u : Int
  D_K : Int
  hu : u ≥ 1
  hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K
  hD : D = u ^ 2 * D_K

/-- Constructor for a fundamental imaginary quadratic discriminant. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_mk {D : Int} (hneg : D < 0)
    (hfund : MetaMathlibExt.IsFundamentalDiscriminant D) :
    IsFundamentalImaginaryQuadraticDiscriminant D :=
  ⟨hneg, hfund⟩
namespace ImaginaryQuadraticDiscriminantDecomposition

/-- Construct a decomposition from its conductor, fundamental discriminant, and equation. -/
def ofFundamental (u D_K : Int) (hu : u ≥ 1)
    (hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K)
    (hD : D = u ^ 2 * D_K) : ImaginaryQuadraticDiscriminantDecomposition D :=
  ⟨u, D_K, hu, hD_K, hD⟩

end ImaginaryQuadraticDiscriminantDecomposition

end ImaginaryQuadraticDiscriminant
