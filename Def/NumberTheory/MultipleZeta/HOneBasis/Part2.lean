/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean -/

import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Theorem.NumberTheory.MultipleZeta.HOneBasis
/-!
# Hoffman basis of `H^1`

Hoffman monomials indexed by all positive compositions, including the empty
index, form a rational basis of the word subalgebra `hOne` from
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/


section

namespace MetaMathlibExt.MultipleZeta

/-- Index decoding an `H^1` word by splitting after each `y`. -/
def indexOfHOneWord (w : FreeMonoid Bool) : Index :=
  ⟨(decodeBlocks (FreeMonoid.toList w)).sum,
    ⟨decodeBlocks (FreeMonoid.toList w),
     fun {i} hi => decodeBlocks_pos (FreeMonoid.toList w) i hi, rfl⟩⟩

end MetaMathlibExt.MultipleZeta
end
