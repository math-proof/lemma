import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main :
-- imply
  TilingC.isFaultfree := by
-- proof
  intro k hk_ge1 hk_lt2
  -- k must be 1 (since 1 ≤ k < 2)
  interval_cases k
  -- k = 1: show there's no fault at column 1
  intro hfault
  obtain ⟨_, _, hdominos⟩ := hfault
  -- The first domino d1 spans columns 1 and 2, so it crosses the potential fault line
  -- d1.minCol = 1 and d1.maxCol = 2, so d1.minCol ≤ 1 ∧ 1 < d1.maxCol
  apply hdominos horizontal_1_1 (by simp only [TilingC, Finset.mem_insert, Finset.mem_singleton, horizontal_1_1]; decide)
  constructor
  ·
    simp only [Domino.minCol]
    decide
  ·
    simp only [Domino.maxCol]
    decide


-- created on 2026-10-20
