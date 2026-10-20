import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


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


private lemma partialWidthSum_succ (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val + 1 < k) :
    partialWidthSum k ts ⟨i.val + 1, hi⟩ = partialWidthSum k ts i + (ts i).1 := by
  simp only [partialWidthSum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.last, Fin.val_mk, Fin.val_castSucc, add_comm]


private lemma point_in_some_component (k : ℕ) (_hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (p : ℤ × ℤ) (hp : p ∈ Rectangle (∑ i : Fin k, (ts i).1) 2) :
    ∃ i : Fin k, (partialWidthSum k ts i : ℤ) < p.1 ∧ 
                  p.1 ≤ partialWidthSum k ts i + (ts i).1 := by
  simp only [Rectangle, Set.mem_ofPred_eq] at hp
  have hp1_pos : p.1 ≥ 1 := hp.1
  have hp1_le : p.1 ≤ ∑ i : Fin k, (ts i).1 := hp.2.1
  -- p.1 - 1 is in range [0, totalWidth - 1]
  have hp1_nat : (p.1 - 1).toNat < ∑ i : Fin k, (ts i).1 := by omega
  -- Find the component using find_component_index
  obtain ⟨i, hi_lo, hi_hi⟩ := find_component_index k (fun j => (ts j).1) (p.1 - 1).toNat hp1_nat
  refine ⟨i, ?_, ?_⟩
  · -- partialWidthSum k ts i < p.1
    simp only [partialWidthSum]
    have h : (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1 : ℤ) ≤ (p.1 - 1).toNat := by
      exact_mod_cast hi_lo
    omega
  · -- p.1 ≤ partialWidthSum k ts i + (ts i).1
    simp only [partialWidthSum]
    have h : ((p.1 - 1).toNat : ℤ) < ∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1 + (ts i).1 := by
      exact_mod_cast hi_hi
    omega


/--
[compose_tilings_dominos_one_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (ts : Fin 1 → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  composeTilings_dominos 1 ts = (ts 0).2.val.dominos := by
-- proof
  simp only [composeTilings_dominos, composeTilings_component_dominos]
  -- Union over Fin 1 is just the single element
  ext d
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨i, d', hd', rfl⟩
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    have h0 : (0 : Fin 1).val = 0 := rfl
    simp only [partialWidthSum_zero 1 ts 0 h0, Domino.shiftNat_zero]
    exact hd'
  · intro hd
    refine ⟨0, d, hd, ?_⟩
    have h0 : (0 : Fin 1).val = 0 := rfl
    simp only [partialWidthSum_zero 1 ts 0 h0, Domino.shiftNat_zero]


-- created on 2026-10-20
