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
import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part9


namespace MetaMathlibExt

namespace CrankNonneg

theorem crk_phi_mem (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) :
    Multiset.count 1 π.parts < (nonOneParts π).length ∧
    Multiset.count 1 π.parts + k <
      phiPivot (Multiset.count 1 π.parts) (nonOneParts π) ∧
    partitionCrank (crkPhi k L hk ⟨π, hπ⟩).1 ≤ -(((k + 1 : ℕ) : ℕ) : ℤ) := by
  obtain ⟨hlen, hbig⟩ := crk_phi_index k L hk π hπ
  exact ⟨hlen, hbig, crkPhiFun_mem k L hk π hπ⟩

theorem crk_psi_mem (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) :
    let c := Multiset.count 1 ν.parts
    let m := nonOneParts ν
    c ≠ 0 ∧ psiCount c m + k + 1 ≤ c ∧ highPartsCond k (crkPsi k L hk ⟨ν, hν⟩).1 := by
  obtain ⟨hne, hbig⟩ := crk_psi_index k L hk ν hν
  exact ⟨hne, hbig, crkPsiFun_mem k L hk ν hν⟩

/-! ## Card equality -/

theorem crk_fun_left_inv (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) :
    crkPsiFun k L hk (crkPhiFun k L hk π hπ)
      (crkPhiFun_mem k L hk π hπ) = π := by
  obtain ⟨hlen, -⟩ := crk_phi_index k L hk π hπ
  have hl_sorted := crk_nonOne_sorted π
  have hpartsΦ : (crkPhiFun k L hk π hπ).parts
      = ((phiList (Multiset.count 1 π.parts) (nonOneParts π) : Multiset ℕ)
        + Multiset.replicate
          (phiPivot (Multiset.count 1 π.parts) (nonOneParts π)) 1) := by
    unfold crkPhiFun
    rw [crkMkPartition_parts]
  have hdecΦ := crk_decode (phiList (Multiset.count 1 π.parts) (nonOneParts π))
    (crk_phi_sorted _ _ hl_sorted hlen) (crk_phi_ge_two _ _ (crk_nonOne_ge_two π))
    (phiPivot (Multiset.count 1 π.parts) (nonOneParts π)) _ hpartsΦ
  have hpartsΨ : (crkPsiFun k L hk (crkPhiFun k L hk π hπ)
      (crkPhiFun_mem k L hk π hπ)).parts
      = (((psiList (Multiset.count 1 (crkPhiFun k L hk π hπ).parts)
          (nonOneParts (crkPhiFun k L hk π hπ)) : Multiset ℕ))
        + Multiset.replicate
          (psiCount (Multiset.count 1 (crkPhiFun k L hk π hπ).parts)
            (nonOneParts (crkPhiFun k L hk π hπ))) 1) := by
    unfold crkPsiFun
    rw [crkMkPartition_parts]
  apply Nat.Partition.ext
  rw [hpartsΨ, hdecΦ.1, hdecΦ.2]
  have hN9 := crk_psi_phi _ _ hl_sorted hlen
  rw [hN9.1, hN9.2]
  exact (crk_parts_eq_nonOne_add π).symm

theorem crk_fun_right_inv (k L : ℕ) (hk : 1 ≤ k) (ν : Nat.Partition L)
    (hν : partitionCrank ν ≤ -(((k + 1 : ℕ) : ℕ) : ℤ)) :
    crkPhiFun k L hk (crkPsiFun k L hk ν hν)
      (crkPsiFun_mem k L hk ν hν) = ν := by
  obtain ⟨-, hbig⟩ := crk_psi_index k L hk ν hν
  have hl_sorted := crk_nonOne_sorted ν
  have hpartsΨ : (crkPsiFun k L hk ν hν).parts
      = (((psiList (Multiset.count 1 ν.parts) (nonOneParts ν) : Multiset ℕ))
        + Multiset.replicate
          (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) 1) := by
    unfold crkPsiFun
    rw [crkMkPartition_parts]
  have hdecΨ := crk_decode (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))
    (crk_psi_sorted (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted)
    (crk_psi_ge_two k _ _ hk hl_sorted (crk_nonOne_ge_two ν) hbig)
    (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν)) _ hpartsΨ
  have hpartsΦ : (crkPhiFun k L hk (crkPsiFun k L hk ν hν)
      (crkPsiFun_mem k L hk ν hν)).parts
      = (((phiList (Multiset.count 1 (crkPsiFun k L hk ν hν).parts)
          (nonOneParts (crkPsiFun k L hk ν hν)) : Multiset ℕ))
        + Multiset.replicate
          (phiPivot (Multiset.count 1 (crkPsiFun k L hk ν hν).parts)
            (nonOneParts (crkPsiFun k L hk ν hν))) 1) := by
    unfold crkPhiFun
    rw [crkMkPartition_parts]
  apply Nat.Partition.ext
  rw [hpartsΦ, hdecΨ.1, hdecΨ.2]
  have hN9 := crk_phi_psi (Multiset.count 1 ν.parts) (nonOneParts ν) hl_sorted
  have hpiv2 : phiPivot (psiCount (Multiset.count 1 ν.parts) (nonOneParts ν))
      (psiList (Multiset.count 1 ν.parts) (nonOneParts ν))
      = Multiset.count 1 ν.parts := hN9.1
  rw [hN9.2, hpiv2]
  exact (crk_parts_eq_nonOne_add ν).symm

end CrankNonneg
end MetaMathlibExt
