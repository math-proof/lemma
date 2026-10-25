/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part3


namespace MetaMathlibExt.PollakPartialParking

theorem parkOcc_succ_of_lt (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) (h : n < s) :
    parkOcc s t g hst (n + 1) =
      insert (parkAssign s t g hst n h) (parkOcc s t g hst n) := by
  simp only [parkOcc, parkOccAux]
  split_ifs
  rfl

theorem parkOcc_succ_of_ge (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) (h : ¬ n < s) :
    parkOcc s t g hst (n + 1) = parkOcc s t g hst n := by
  simp only [parkOcc, parkOccAux]
  split_ifs
  rfl

theorem parkOcc_subset_succ (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) : parkOcc s t g hst n ⊆ parkOcc s t g hst (n + 1) := by
  by_cases h : n < s
  · rw [parkOcc_succ_of_lt s t g hst n h]
    exact Finset.subset_insert _ _
  · rw [parkOcc_succ_of_ge s t g hst n h]

theorem parkOcc_mono (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    Monotone (parkOcc s t g hst) :=
  monotone_nat_of_le_succ (parkOcc_subset_succ s t g hst)

theorem parkAssign_mem (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) (h : n < s) :
    parkAssign s t g hst n h ∈ parkOcc s t g hst (n + 1) := by
  rw [parkOcc_succ_of_lt s t g hst n h]
  exact Finset.mem_insert_self _ _

theorem parkAssign_mem_of_le (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (a b : ℕ) (ha : a < s) (hab : a + 1 ≤ b) :
    parkAssign s t g hst a ha ∈ parkOcc s t g hst b :=
  parkOcc_mono s t g hst hab (parkAssign_mem s t g hst a ha)

theorem parkAssign_inj (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (a b : ℕ) (ha : a < s) (hb : b < s) (hne : a ≠ b) :
    parkAssign s t g hst a ha ≠ parkAssign s t g hst b hb := by
  rcases lt_trichotomy a b with hab | hab | hab
  · intro heq
    have hmem : parkAssign s t g hst b hb ∈ parkOcc s t g hst b := by
      rw [← heq]
      exact parkAssign_mem_of_le s t g hst a b ha (by omega)
    exact firstFree_not_mem t (parkOcc s t g hst b) (g ⟨b, hb⟩) _ hmem
  · exact absurd hab hne
  · intro heq
    have hmem : parkAssign s t g hst a ha ∈ parkOcc s t g hst a := by
      rw [heq]
      exact parkAssign_mem_of_le s t g hst b a hb (by omega)
    exact firstFree_not_mem t (parkOcc s t g hst a) (g ⟨a, ha⟩) _ hmem

theorem card_parkOcc_self (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    (parkOcc s t g hst s).card = s := by
  apply le_antisymm (card_parkOcc_le s t g hst s)
  have hinj : Function.Injective
      (fun k : Fin s => parkAssign s t g hst k.val k.isLt) := by
    intro k1 k2 h12
    simp only at h12
    by_cases hne : k1.val ≠ k2.val
    · exact absurd h12 (parkAssign_inj s t g hst k1.val k2.val k1.isLt k2.isLt hne)
    · exact Fin.ext (not_not.mp hne)
  have hsub : Finset.univ.image (fun k : Fin s => parkAssign s t g hst k.val k.isLt)
      ⊆ parkOcc s t g hst s := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact parkAssign_mem_of_le s t g hst k.val s k.isLt (by omega)
  have hle := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin] at hle

end MetaMathlibExt.PollakPartialParking
