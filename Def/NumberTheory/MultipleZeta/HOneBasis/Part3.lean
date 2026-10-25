/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean -/

import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Theorem.NumberTheory.MultipleZeta.HOneBasis.Part2
/-!
# Hoffman basis of `H^1`

Hoffman monomials indexed by all positive compositions, including the empty
index, form a rational basis of the word subalgebra `hOne` from
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/


section

namespace MetaMathlibExt.MultipleZeta

/-- Linear-equiv version of the free-algebra identification. -/
noncomputable def freeAlgEquiv :
    FreeAlgebra ℚ Bool ≃ₗ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool) :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
    FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)).toLinearEquiv

end MetaMathlibExt.MultipleZeta
end
