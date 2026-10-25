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
import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part8


namespace MetaMathlibExt

namespace CrankNonneg

theorem crkPsiFun_mem (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) :
    highPartsCond k (crkPsiFun k L hk ν hν) := by
  obtain ⟨-, hbig⟩ := crk_psi_index k L hk ν hν
  have hl_sorted := crk_nonOne_sorted ν
  have hsorted' :=
    crk_psi_sorted (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted
  have hparts : (crkPsiFun k L hk ν hν).parts
      = (((psiList (Multiset.count 1 ν.parts) (nonOneParts ν) : Multiset ℕ))
        + Multiset.replicate
          (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) 1) := by
    unfold crkPsiFun
    rw [crkMkPartition_parts]
  have hdec := crk_decode (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))
    hsorted'
    (crk_psi_ge_two k _ _ hk hl_sorted (crk_nonOne_ge_two ν) hbig)
    (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) _ hparts
  have hω := hdec.1
  have hnon := hdec.2
  have hlen_b : psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)
      < (psiList (Multiset.count 1 ν.parts) (nonOneParts ν)).length :=
    crk_psi_length (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted
  have hpivget : (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))[
      psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)]'hlen_b
      = Multiset.count 1 ν.parts := by
    have hpiv : (psiList (Multiset.count 1 ν.parts) (nonOneParts ν)).getD
        (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) 0
        = Multiset.count 1 ν.parts :=
      crk_psi_pivot (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted
    rwa [List.getD_eq_getElem _ _ hlen_b] at hpiv
  have hlt : psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) + k
      < (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))[
        psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)]'hlen_b := by
    rw [hpivget]
    omega
  have hiff := crk_mem_filter_iff
    (psiList (Multiset.count 1 ν.parts) (nonOneParts ν)) hsorted'
    (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) + k)
    (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) hlen_b
  unfold highPartsCond
  rw [hω]
  have h1k : 1 ≤ psiCount (Multiset.count 1 ν.parts) (nonOneParts ν) + k := by
    omega
  rw [crk_filter_threshold _ _ h1k, hnon]
  exact hiff.mpr hlt

end CrankNonneg
end MetaMathlibExt
