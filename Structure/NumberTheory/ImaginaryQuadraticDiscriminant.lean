/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/

import Def.NumberTheory.DirichletCharacter.Quadratic
import Lemma.Nat.DirichletCharacter.Quadratic
import Def.NumberTheory.ImaginaryQuadraticDiscriminant
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
