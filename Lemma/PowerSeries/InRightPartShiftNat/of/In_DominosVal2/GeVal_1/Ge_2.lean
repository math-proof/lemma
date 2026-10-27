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
[compose_tilings_component_pos_in_right_part_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (i : Fin k)
  (d : Domino)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hi : i.val ≥ 1)
  (hd : d ∈ (ts i).2.val.dominos) :
-- imply
  (d.shiftNat (partialWidthSum k ts i)).inRightPart (ts ⟨0, by omega⟩).1 := by
-- proof
  intro p hp
  -- The shifted domino has x-coordinates >= partialWidthSum k ts i + 1
  -- Since i >= 1, partialWidthSum k ts i >= (ts 0).1
  have hpws_ge : partialWidthSum k ts i ≥ (ts ⟨0, by omega⟩).1 := by
    have h0 : (⟨0, by omega⟩ : Fin k) < i := by simp [Fin.lt_def]; omega
    have := partialWidthSum_add_le k ts ⟨0, by omega⟩ i h0
    omega
  -- The original domino d has x-coords in [1, (ts i).1]
  have hd_x := domino_subset_rect (ts i).1 (ts i).2.val d hd
  -- After shifting, x-coords are in [1 + pws, (ts i).1 + pws]
  rw [Domino.shiftNat_toShape, Set.mem_image] at hp
  obtain ⟨p', hp', hp_eq⟩ := hp
  rw [Prod.ext_iff] at hp_eq
  have hp'_rect := hd_x hp'
  simp only [Rectangle, Set.mem_ofPred_eq] at hp'_rect
  have hx' : p'.1 ≥ 1 := hp'_rect.1
  calc p.1 = p'.1 + partialWidthSum k ts i := by omega
    _ ≥ 1 + (ts ⟨0, by omega⟩).1 := by omega
    _ = (ts ⟨0, by omega⟩).1 + 1 := by ring


-- created on 2026-10-20
