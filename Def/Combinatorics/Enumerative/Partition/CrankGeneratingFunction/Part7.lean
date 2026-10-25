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
import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part5


namespace MetaMathlibExt

namespace CrankNonneg

noncomputable def crkPhi (k L : ℕ) (hk : 1 ≤ k)
    (π : { π : Nat.Partition L // highPartsCond k π }) :
    { ν : Nat.Partition L // partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) } :=
  ⟨crkPhiFun k L hk π.1 π.2, crkPhiFun_mem k L hk π.1 π.2⟩

end CrankNonneg
end MetaMathlibExt
