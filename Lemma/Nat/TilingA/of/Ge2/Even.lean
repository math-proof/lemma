import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


-- Private helpers (ported from sympy DominoTilings; file-local)

private lemma middleDominos_mem (n i : ℕ) (hi : i < n / 2 - 1) :
    ∃ d ∈ middleDominos n, d.cell1 = (2 * i + 2, 2) ∧ d.cell2 = (2 * i + 3, 2) := by
  simp only [middleDominos, Finset.mem_map, Finset.mem_range]
  refine ⟨_, ⟨i, hi, rfl⟩, rfl, rfl⟩

private lemma basementDominos_mem (n i : ℕ) (hi : i < n / 2) :
    ∃ d ∈ basementDominos n, d.cell1 = (2 * i + 1, 1) ∧ d.cell2 = (2 * i + 2, 1) := by
  simp only [basementDominos, Finset.mem_map, Finset.mem_range]
  refine ⟨_, ⟨i, hi, rfl⟩, rfl, rfl⟩

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  (TilingA n hn hn_ge).isFaultfree := by
-- proof
  intro k hk_ge1 hk_lt_n
  unfold DominoTiling.hasFaultAt
  push Not
  intro _ _
  -- We need to find a domino that spans column k
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · -- k is even, so k = 2j for some j ≥ 1
    obtain ⟨j, hj⟩ := hk_even
    have hj_pos : j ≥ 1 := by omega
    have hj_bound : j - 1 < n / 2 - 1 := by
      have hn2 : n / 2 * 2 = n := Nat.div_two_mul_two_of_even hn
      have : k < n := hk_lt_n
      have : j + j < n := by omega
      have : j < n / 2 := by omega
      omega
    -- The middle domino at index j-1 spans columns 2j to 2j+1
    obtain ⟨d, hd_mem, hd1, hd2⟩ := middleDominos_mem n (j - 1) hj_bound
    use d
    constructor
    · -- Show this domino is in the tiling
      simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
      left; right
      exact hd_mem
    · -- Show it spans column k
      simp only [Domino.minCol, Domino.maxCol, hd1, hd2]
      have h1 : 2 * (j - 1) + 2 = 2 * j := by omega
      have h2 : 2 * (j - 1) + 3 = 2 * j + 1 := by omega
      constructor
      · -- minCol ≤ k
        simp only [min_def]
        split_ifs <;> omega
      · -- k < maxCol
        simp only [max_def]
        split_ifs <;> omega
  · -- k is odd, so k = 2j + 1 for some j ≥ 0
    obtain ⟨j, hj⟩ := hk_odd
    have hj_bound : j < n / 2 := by
      have hn2 : n / 2 * 2 = n := Nat.div_two_mul_two_of_even hn
      have : k < n := hk_lt_n
      have : 2 * j + 1 < n := by omega
      omega
    -- The basement domino at index j spans columns (2j+1) to (2j+2)
    obtain ⟨d, hd_mem, hd1, hd2⟩ := basementDominos_mem n j hj_bound
    use d
    constructor
    · -- Show this domino is in the tiling
      simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
      left; left; left; left
      exact hd_mem
    · -- Show it spans column k
      simp only [Domino.minCol, Domino.maxCol, hd1, hd2]
      constructor
      · -- minCol ≤ k
        simp only [min_def]
        split_ifs <;> omega
      · -- k < maxCol
        simp only [max_def]
        split_ifs <;> omega


-- created on 2026-10-20
