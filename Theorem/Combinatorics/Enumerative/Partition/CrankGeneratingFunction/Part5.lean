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
import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part6


namespace MetaMathlibExt

namespace CrankNonneg

theorem crkPhiFun_mem (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) :
    partitionCrank (crkPhiFun k L hk π hπ) ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) := by
  obtain ⟨hlen, hbig⟩ := crk_phi_index k L hk π hπ
  have hl_sorted := crk_nonOne_sorted π
  have h2_sorted := crk_nonOne_ge_two π
  have hpiv : phiPivot (Multiset.count 1 π.parts) (nonOneParts π)
      = (nonOneParts π)[Multiset.count 1 π.parts]'hlen :=
    List.getD_eq_getElem _ _ hlen
  have hbig' : Multiset.count 1 π.parts + k
      < (nonOneParts π)[Multiset.count 1 π.parts]'hlen := by
    rw [← hpiv]
    exact hbig
  have hparts : (crkPhiFun k L hk π hπ).parts
      = ((phiList (Multiset.count 1 π.parts) (nonOneParts π) : Multiset ℕ)
        + Multiset.replicate
          (phiPivot (Multiset.count 1 π.parts) (nonOneParts π)) 1) := by
    unfold crkPhiFun
    rw [crkMkPartition_parts]
  have hdec := crk_decode (phiList (Multiset.count 1 π.parts) (nonOneParts π))
    (crk_phi_sorted _ _ hl_sorted hlen) (crk_phi_ge_two _ _ h2_sorted)
    (phiPivot (Multiset.count 1 π.parts) (nonOneParts π)) _ hparts
  have hω := hdec.1
  have hnon := hdec.2
  have hpivbig := crk_phi_pivot_big k _ _ hlen hbig'
  have hωpos : 1 ≤ phiPivot (Multiset.count 1 π.parts) (nonOneParts π) := by
    omega
  have hne : Multiset.count 1 (crkPhiFun k L hk π hπ).parts ≠ 0 := by omega
  have hcrank : partitionCrank (crkPhiFun k L hk π hπ)
      = ((Multiset.count 1 π.parts : ℕ) : ℤ)
        - ((phiPivot (Multiset.count 1 π.parts) (nonOneParts π) : ℕ) : ℤ) := by
    unfold partitionCrank
    split
    · next hcon => exact absurd hcon hne
    · next _ =>
        rw [hω, crk_filter_threshold _ _ hωpos, hnon,
          crk_phi_filter _ _ hl_sorted hlen]
  rw [hcrank]
  omega

end CrankNonneg
end MetaMathlibExt
