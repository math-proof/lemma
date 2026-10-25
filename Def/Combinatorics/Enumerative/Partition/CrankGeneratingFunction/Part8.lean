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
import Theorem.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part6


namespace MetaMathlibExt

namespace CrankNonneg

noncomputable def crkPsiFun (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) : Nat.Partition L :=
  crkMkPartition L (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν))
    (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))
    (fun x hx => by
      have hbig2 := (crk_psi_index k L hk ν hν).2
      have hge := crk_psi_ge_two k _ _ hk (crk_nonOne_sorted ν)
        (crk_nonOne_ge_two ν) hbig2 x hx
      omega)
    (by
      have hbig2 := (crk_psi_index k L hk ν hν).2
      have hsum : psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)
          + (psiList (Multiset.count 1 ν.parts) (nonOneParts ν)).sum
          = Multiset.count 1 ν.parts + (nonOneParts ν).sum :=
        crk_psi_sum _ _ (crk_nonOne_ge_two ν)
      have hωsum := crk_omega_add_sum ν
      omega)

end CrankNonneg
end MetaMathlibExt
