module
public import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
public import Theorem.Nat.MultipleZeta.WordAlgebra
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace


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

def encBlock (n : Nat) : List Bool :=
  List.replicate (n - 1) false ++ [true]

def encList (l : List Nat) : List Bool :=
  (l.map encBlock).flatten

def decAux : List Bool → Nat → List Nat
  | [], n => if n = 0 then [] else [n + 1]
  | false :: t, n => decAux t (n + 1)
  | true :: t, n => (n + 1) :: decAux t 0

end MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted
end
