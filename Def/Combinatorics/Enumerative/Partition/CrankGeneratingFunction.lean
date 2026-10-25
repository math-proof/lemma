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


namespace MetaMathlibExt

namespace CrankNonneg

/-- Crank of a partition, using exactly the expression from the `Wanted` entry:
the largest part when no part equals `1`, else the number of parts exceeding
the number of ones minus the number of ones. -/
def partitionCrank {M : ℕ} (P : Nat.Partition M) : ℤ :=
  if Multiset.count 1 P.parts = 0 then (P.parts.sup : ℤ)
  else (((P.parts.filter (fun i => Multiset.count 1 P.parts < i)).card : ℤ) -
    (Multiset.count 1 P.parts : ℤ))

/-- Number `D(k, M)` of partitions of `M` with crank at most `-k`. -/
def crankLeCount (k M : ℕ) : ℕ :=
  Fintype.card { P : Nat.Partition M // partitionCrank P ≤ -(k : ℤ) }

/-- Membership condition for `U_k(L)`: at least `ω(π) + 1` parts exceed `ω(π) + k`. -/
def highPartsCond (k : ℕ) {L : ℕ} (π : Nat.Partition L) : Prop :=
  Multiset.count 1 π.parts + 1 ≤
    (π.parts.filter (fun x => Multiset.count 1 π.parts + k < x)).card

end CrankNonneg
end MetaMathlibExt
