/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/

import Def.NumberTheory.DirichletCharacter.Quadratic
import Lemma.Nat.DirichletCharacter.Quadratic
import Theorem.NumberTheory.ImaginaryQuadraticDiscriminant
set_option autoImplicit false

/-!
# Imaginary quadratic discriminants

This file specializes the canonical predicate `MetaMathlibExt.IsFundamentalDiscriminant` to
negative discriminants and packages conductor--fundamental-discriminant decompositions.
-/


namespace ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminantDecomposition

/-- Construct a decomposition from its conductor, fundamental discriminant, and equation. -/
def ofFundamental (u D_K : Int) (hu : u ≥ 1)
    (hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K)
    (hD : D = u ^ 2 * D_K) : ImaginaryQuadraticDiscriminantDecomposition D :=
  ⟨u, D_K, hu, hD_K, hD⟩

end ImaginaryQuadraticDiscriminantDecomposition
end ImaginaryQuadraticDiscriminant
