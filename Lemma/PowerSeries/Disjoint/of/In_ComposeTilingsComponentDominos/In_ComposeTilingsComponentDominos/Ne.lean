import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


private lemma domino_subset_rect (n : ℕ) (T : Tiling (Rectangle n 2)) (d : Domino) (hd : d ∈ T.dominos) :
    d.toShape ⊆ Rectangle n 2 := by
  intro x hx
  have : x ∈ ⋃ d ∈ T.dominos, d.toShape := by
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hx⟩
  rw [T.cover] at this
  exact this


private lemma shifted_domino_x_in_range' {n : ℕ} {T : Tiling (Rectangle n 2)} {d : Domino}
    (hd : d ∈ T.dominos) (offset : ℕ) (p : ℤ × ℤ) (hp : p ∈ (d.shiftNat offset).toShape) :
    1 + (offset : ℤ) ≤ p.1 ∧ p.1 ≤ n + (offset : ℤ) := by
  rw [Domino.shiftNat_toShape] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  have hsub := domino_subset_rect n T d hd hp'
  simp only [Rectangle, Set.mem_ofPred_eq] at hsub
  simp only
  constructor <;> linarith


private lemma find_component_index (k : ℕ) (widths : Fin k → ℕ) (x : ℕ) (hx : x < ∑ i, widths i) :
    ∃ i : Fin k, (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) ≤ x ∧ 
                 x < (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) + widths i := by
  induction k with
  | zero => 
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hx
    omega
  | succ k ih =>
    by_cases h : x < ∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    · have ih' := ih (fun i => widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) h
      obtain ⟨i, hi1, hi2⟩ := ih'
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi1, hi2⟩
    · push Not at h
      have hsum : ∑ i : Fin (k + 1), widths i = 
          (∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + widths ⟨k, Nat.lt_succ_self k⟩ := by
        rw [Fin.sum_univ_castSucc]
        rfl
      have hx' : x < (∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + widths ⟨k, Nat.lt_succ_self k⟩ := by
        calc x < ∑ i : Fin (k + 1), widths i := hx
          _ = _ := hsum
      exact ⟨⟨k, Nat.lt_succ_self k⟩, h, hx'⟩


private lemma partialWidthSum_add_le (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i1 i2 : Fin k) (h : i1 < i2) :
    partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := by
  simp only [partialWidthSum]
  have hi : i1.val < i2.val := h
  have hle : i1.val + 1 ≤ i2.val := hi
  have hk : i1.val + 1 < k := Nat.lt_of_le_of_lt hi i2.isLt
  have hinj : Function.Injective (Fin.castLE hle) := Fin.castLE_injective hle
  have step1 : (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1 = 
               ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := by
    have heq := Fin.sum_univ_castSucc (fun j : Fin (i1.val + 1) => (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1)
    simp only [Fin.last, Fin.val_mk, Fin.val_castSucc] at heq
    linarith [heq]
  calc (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1
      = ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := step1
    _ = ∑ j : Fin (i1.val + 1), (ts ⟨(Fin.castLE hle j).val, Nat.lt_trans (Fin.castLE hle j).isLt i2.isLt⟩).1 := by
          apply Finset.sum_congr rfl; intro x _; simp [Fin.castLE]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (i1.val + 1))).map ⟨Fin.castLE hle, hinj⟩, 
          (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          rw [Finset.sum_map]; simp
    _ ≤ ∑ j : Fin i2.val, (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          apply Finset.sum_le_univ_sum_of_nonneg; intro _; exact Nat.zero_le _


/--
[compose_tilings_component_dominos_disjoint_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (i1 i2 : Fin k)
  (d1 d2 : Domino)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hi : i1 ≠ i2)
  (hd1 : d1 ∈ composeTilings_component_dominos k ts i1)
  (hd2 : d2 ∈ composeTilings_component_dominos k ts i2) :
-- imply
  Disjoint d1.toShape d2.toShape := by
-- proof
  -- Get the original dominos
  simp only [composeTilings_component_dominos, Set.mem_image] at hd1 hd2
  obtain ⟨d1', hd1', rfl⟩ := hd1
  obtain ⟨d2', hd2', rfl⟩ := hd2
  -- WLOG i1 < i2
  wlog h : i1 < i2 generalizing i1 i2 d1' d2' with H
  · have h' : i2 < i1 := (lt_or_gt_of_ne hi).resolve_left h
    exact (H i2 i1 (Ne.symm hi) d2' hd2' d1' hd1' h').symm
  -- Key: partialWidthSum i1 + (ts i1).1 ≤ partialWidthSum i2
  have key : partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := 
    partialWidthSum_add_le k ts i1 i2 h
  -- Prove disjointness using x-coordinate separation
  rw [Set.disjoint_iff]
  intro p ⟨hp1, hp2⟩
  have hx1 := shifted_domino_x_in_range' hd1' (partialWidthSum k ts i1) p hp1
  have hx2 := shifted_domino_x_in_range' hd2' (partialWidthSum k ts i2) p hp2
  have h1 : p.1 ≤ (ts i1).1 + partialWidthSum k ts i1 := hx1.2
  have h2 : 1 + partialWidthSum k ts i2 ≤ p.1 := hx2.1
  have h3 : (ts i1).1 + partialWidthSum k ts i1 < 1 + partialWidthSum k ts i2 := by
    calc (ts i1).1 + partialWidthSum k ts i1 
        = partialWidthSum k ts i1 + (ts i1).1 := by ring
      _ ≤ partialWidthSum k ts i2 := key
      _ < 1 + partialWidthSum k ts i2 := by omega
  linarith


-- created on 2026-10-20
