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
private lemma main
  {n m : ℕ}
  {c : Cell} :
-- imply
  c ∈ Rectangle n m ↔ c.1 ≥ 1 ∧ c.1 ≤ n ∧ c.2 ≥ 1 ∧ c.2 ≤ m := by
-- proof
  simp only [Rectangle, Finset.mem_map, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  ·
    rintro ⟨x, y, ⟨hx, hy⟩, h⟩
    have : c = (x + 1, y + 1) := h.symm
    simp only [this]
    omega
  ·
    rintro ⟨h1, h2, h3, h4⟩
    refine ⟨c.1 - 1, c.2 - 1, ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    ·
      show (c.1 - 1 + 1, c.2 - 1 + 1) = c
      ext <;> omega


-- created on 2026-10-20
