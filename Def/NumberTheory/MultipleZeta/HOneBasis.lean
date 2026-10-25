/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean -/

import Theorem.NumberTheory.MultipleZeta.WordAlgebra.Part2
import Lemma.Nat.MultipleZeta.WordAlgebra
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.DFinsupp
/-!
# Hoffman basis of `H^1`

Hoffman monomials indexed by all positive compositions, including the empty
index, form a rational basis of the word subalgebra `hOne` from
`MathlibExt.NumberTheory.MultipleZeta.WordAlgebra`.
-/


section

namespace MetaMathlibExt.MultipleZeta

/-- Increment the leading block size; auxiliary for `decodeBlocks`. -/
def bump : List Nat → List Nat
  | [] => []
  | k :: ks => (k + 1) :: ks

/-- Encode a list of block sizes as a word over `{x, y}`. -/
def encodeNatBlocks : List Nat → List Bool
  | [] => []
  | k :: ks => List.replicate (k - 1) false ++ [true] ++ encodeNatBlocks ks

/-- Decode a word over `{x, y}` into block sizes, dropping a trailing
open `x`-run (which never occurs for `H^1` words). -/
def decodeBlocks : List Bool → List Nat
  | [] => []
  | true :: rest => 1 :: decodeBlocks rest
  | false :: rest => bump (decodeBlocks rest)

end MetaMathlibExt.MultipleZeta
end
