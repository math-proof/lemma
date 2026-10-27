import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (n i : ℕ)
  (hi : i < n / 2 - 1) :
-- imply
  ∃ d ∈ middleDominos n, d.cell1 = (2 * i + 2, 2) ∧ d.cell2 = (2 * i + 3, 2) := by
-- proof
  simp only [middleDominos, Finset.mem_map, Finset.mem_range]
  refine ⟨_, ⟨i, hi, rfl⟩, rfl, rfl⟩


-- created on 2026-10-20
