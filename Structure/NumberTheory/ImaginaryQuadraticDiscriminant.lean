/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/

module

public import Def.NumberTheory.DirichletCharacter.Quadratic
public import Theorem.Nat.DirichletCharacter.Quadratic
public import Def.NumberTheory.ImaginaryQuadraticDiscriminant
public section

set_option autoImplicit false

/-!
# Imaginary quadratic discriminants

This file specializes the canonical predicate `MetaMathlibExt.IsFundamentalDiscriminant` to
negative discriminants and packages conductor--fundamental-discriminant decompositions.
-/


namespace ImaginaryQuadraticDiscriminant

/-- A decomposition `D = u ^ 2 * D_K` into a positive conductor and a fundamental imaginary
quadratic discriminant. -/
structure ImaginaryQuadraticDiscriminantDecomposition (D : Int) where
  u : Int
  D_K : Int
  hu : u ≥ 1
  hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K
  hD : D = u ^ 2 * D_K

end ImaginaryQuadraticDiscriminant
