/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/UnionClosedOrderly.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Lex
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Fin.Tuple.Take


namespace MetaMathlibExt

/-! # Orderly canonical prefixes of union-closed sets

This file proves that every nonempty initial segment of a canonical indexed family is canonical.
-/

/-- Binary code `b(A)` of a subset `A ⊆ Ω_n`: the sum of `2^i` over `i ∈ A`. -/
def binRep (n : ℕ) (A : Finset (Fin n)) : ℕ :=
  ∑ i ∈ A, 2 ^ (i : ℕ)

/-- The paper's strict order on subsets: `A < B` iff `|A| > |B|`, or the
cardinalities agree and `b(A) < b(B)`. -/
def setLT (n : ℕ) (A B : Finset (Fin n)) : Prop :=
  B.card < A.card ∨ (A.card = B.card ∧ binRep n A < binRep n B)

/-- Sort key encoding the paper's set order as one natural number:
`(n - |A|) * 2^n + b(A)`. Since `b(A) < 2^n`, numeric key order agrees with
the paper's set order. -/
def setKey (n : ℕ) (A : Finset (Fin n)) : ℕ :=
  (n - A.card) * 2 ^ n + binRep n A

/-- The paper's string `s(U)`: sort keys of the nonempty members of `U`,
in increasing order. -/
def famString (n : ℕ) (U : Finset (Finset (Fin n))) : List ℕ :=
  Multiset.sort ((U.filter (· ≠ ∅)).val.map (setKey n)) (· ≤ ·)

/-- Action of a universe permutation on a family: apply `σ` to every element
of every member. -/
def permImage (n : ℕ) (σ : Equiv.Perm (Fin n))
    (U : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  U.image fun A => A.image ⇑σ

/-- A family is union-closed if it contains the union of any two members. -/
def IsUnionClosed (n : ℕ) (U : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ U, ∀ B ∈ U, A ∪ B ∈ U

/-- A family is the canonical representative of its isomorphism class if its
string is lexicographically minimal among all permuted images (`≤` on
`List ℕ` is the lexicographic order). -/
def IsCanonical (n : ℕ) (U : Finset (Finset (Fin n))) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), famString n U ≤ famString n (permImage n σ U)

end MetaMathlibExt
