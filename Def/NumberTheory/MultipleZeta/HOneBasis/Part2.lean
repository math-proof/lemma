module
public import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
public import Theorem.Nat.MultipleZeta.WordAlgebra
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Theorem.NumberTheory.MultipleZeta.HOneBasis


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean -/
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
