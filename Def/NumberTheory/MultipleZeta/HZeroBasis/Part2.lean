module
public import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
public import Theorem.Nat.MultipleZeta.WordAlgebra
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Theorem.NumberTheory.MultipleZeta.HZeroBasis


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean -/
/-!
# Multiple-zeta word bases

This file records the two substantial basis constructions left after the
proved word-subalgebra interface in
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/
section

namespace MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted

open MetaMathlibExt.MultipleZeta

def emptyIndex : Index :=
  ⟨0, Composition.mk [] (by simp) rfl⟩

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted
end
