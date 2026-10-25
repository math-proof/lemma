/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Instance.Combinatorics.Enumerative.Partition.CrankGeneratingFunction


namespace MetaMathlibExt

namespace CrankNonneg

/-- The non-one parts of a partition, sorted weakly decreasing. -/
def nonOneParts {n : ℕ} (P : Nat.Partition n) : List ℕ :=
  (P.parts.filter (2 ≤ ·)).sort (· ≥ ·)

/-- Forward list map: add one to each of the first `a` entries, drop entry `a`. -/
def phiList (a : ℕ) (l : List ℕ) : List ℕ :=
  (List.take a l).map (· + 1) ++ List.drop (a + 1) l

/-- Pivot value for `phiList`. -/
def phiPivot (a : ℕ) (l : List ℕ) : ℕ := l.getD a 0

/-- Number of entries of `m` exceeding `c`. -/
def psiCount (c : ℕ) (m : List ℕ) : ℕ :=
  (m.filter (fun x => decide (c < x))).length

/-- Backward list map. -/
def psiList (c : ℕ) (m : List ℕ) : List ℕ :=
  (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m

/-- Staircase offset `e(k, m) = (m + 1) * m / 2 + m * (k - 1)`. -/
def crkE (k m : ℕ) : ℕ := (m + 1) * m / 2 + m * (k - 1)

/-- Alternating partition sum `S(k, M)`. -/
def crankAltSum (k M : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (M + 1),
    if crkE k m ≤ M then
      (-1 : ℤ) ^ m * (Fintype.card (Nat.Partition (M - crkE k m)) : ℤ)
    else 0

end CrankNonneg
end MetaMathlibExt
