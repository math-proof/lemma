/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part13


section

namespace MetaMathlibExt

theorem mpePerms_card_sum (d : ℕ) :
    (mpePerms d).card =
      ∑ a ∈ mpePositions d, (mpeAllowedAt d a).card := by
  classical
  have hmaps : (↑(mpePerms d) : Set (Equiv.Perm (Fin (d + 2)))).MapsTo
      (mpeAscentPos d) (mpePositions d) := by
    intro σ hσ
    have hgood := (mpePerms_mem d σ).mp hσ
    obtain ⟨hpos, hlt, _, _⟩ := mpeAscentPos_spec d σ hgood
    exact (mpePositions_mem d (mpeAscentPos d σ)).mpr ⟨hpos, hlt⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨hpos, hlt⟩ := (mpePositions_mem d a).mp ha
  change (mpeFiber d a).card = (mpeAllowedAt d a).card
  rw [mpeAllowedAt_eq d a hpos]
  exact mpeFiber_card_allowed d a hpos hlt

theorem mpeAllowed_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (mpeAllowed d a hpos).card = Nat.choose (d + 2) (a.val + 1) - (d + 2) := by
  rw [mpeAllowed, Finset.card_sdiff_of_subset (mpe_excl_union_subset d a hpos)]
  rw [Finset.card_powersetCard, exclUnion_card d a hpos]
  simp only [Finset.card_univ, Fintype.card_fin]

theorem mpeAllowed_card_add (d : ℕ) (a : Fin (d + 1))
    (hpos : 0 < a.val) :
    (mpeAllowed d a hpos).card + (d + 2) = Nat.choose (d + 2) (a.val + 1) := by
  have hle := Finset.card_le_card (mpe_excl_union_subset d a hpos)
  rw [exclUnion_card d a hpos, Finset.card_powersetCard] at hle
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  have hcard := mpeAllowed_card d a hpos
  omega

theorem mpePerms_card_add (d : ℕ) (hd : 2 ≤ d) :
    (mpePerms d).card + (d + 1) * (d + 2) + 2 = 2 ^ (d + 2) := by
  have hterms :
      (mpePositions d).sum (fun a => (mpeAllowedAt d a).card + (d + 2)) =
        (mpePositions d).sum (fun a => Nat.choose (d + 2) (a.val + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    obtain ⟨hpos, _⟩ := (mpePositions_mem d a).mp ha
    rw [mpeAllowedAt_eq d a hpos]
    exact mpeAllowed_card_add d a hpos
  rw [Finset.sum_add_distrib] at hterms
  simp only [Finset.sum_const, nsmul_eq_mul] at hterms
  rw [mpePositions_card d] at hterms
  have hterms' :
      (∑ a ∈ mpePositions d, (mpeAllowedAt d a).card) +
        (d - 1) * (d + 2) =
          ∑ a ∈ mpePositions d, Nat.choose (d + 2) (a.val + 1) := by
    simpa using hterms
  have hcard := mpePerms_card_sum d
  have hchoose := mpe_choose_sum_positions d hd
  have hd' : d + 1 = (d - 1) + 2 := by omega
  have hfactor : (d + 1) * (d + 2) =
      (d - 1) * (d + 2) + 2 * (d + 2) := by
    rw [hd', Nat.add_mul]
  rw [hcard, hfactor]
  calc
    _ = ((∑ a ∈ mpePositions d, (mpeAllowedAt d a).card) +
          (d - 1) * (d + 2)) + 2 * (d + 2) + 2 := by ac_rfl
    _ = (∑ a ∈ mpePositions d, Nat.choose (d + 2) (a.val + 1)) +
          2 * (d + 2) + 2 := by rw [hterms']
    _ = 2 ^ (d + 2) := hchoose

/--
The number of minimal permutations with `d` descents and size `d + 2`.
Minimality means deleting any one entry leaves fewer than `d` descents.
Source: Stefano Bilotta, Elisabetta Grazzini, and Elisa Pergola, "Enumeration of Two Particular Sets of Minimal Permutations", Journal of Integer Sequences 18 (2015), Article 15.10.2, Theorem `thm:enum`, lines 324-326, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Grazzini/graz3.tex>.

Proves `Wanted` entry `minimal_permutations_card`.
-/
theorem minimal_permutations_card (d : ℕ) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 2)) =>
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc > σ i.succ).card = d ∧
      ∀ j : Fin (d + 2),
        (Finset.univ.filter fun i : Fin d =>
          σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d).card =
      2 ^ (d + 2) - (d + 1) * (d + 2) - 2 := by
  classical
  have hset : (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 2)) =>
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc > σ i.succ).card = d ∧
      ∀ j : Fin (d + 2),
        (Finset.univ.filter fun i : Fin d =>
          σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d) =
      mpePerms d := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mpePerms_mem, mpeGood]
  rw [hset]
  by_cases hd : 2 ≤ d
  · have hadd := mpePerms_card_add d hd
    omega
  · have hsmall : d = 0 ∨ d = 1 := by omega
    rcases hsmall with rfl | rfl
    · have hcard := mpePerms_card_sum 0
      have hempty : mpePositions 0 = ∅ := Finset.card_eq_zero.mp (by
        rw [mpePositions_card])
      rw [hempty] at hcard
      simp only [Finset.sum_empty] at hcard
      norm_num [hcard]
    · have hcard := mpePerms_card_sum 1
      have hempty : mpePositions 1 = ∅ := Finset.card_eq_zero.mp (by
        rw [mpePositions_card])
      rw [hempty] at hcard
      simp only [Finset.sum_empty] at hcard
      norm_num [hcard]

end MetaMathlibExt
end
