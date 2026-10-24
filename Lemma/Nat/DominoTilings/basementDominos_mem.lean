import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
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
  (hi : i < n / 2) :
-- imply
  ∃ d ∈ basementDominos n, d.cell1 = (2 * i + 1, 1) ∧ d.cell2 = (2 * i + 2, 1) := by
-- proof
  simp only [basementDominos, Finset.mem_map, Finset.mem_range]
  refine ⟨_, ⟨i, hi, rfl⟩, rfl, rfl⟩


-- created on 2026-10-20
