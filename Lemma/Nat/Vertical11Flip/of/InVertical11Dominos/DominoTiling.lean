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
-- given
  (T : DominoTiling n m)
  (hv : vertical_1_1 ∈ T.dominos) :
-- imply
  vertical_1_1_flip ∉ T.dominos := by
-- proof
  intro hvf
  have hne : vertical_1_1 ≠ vertical_1_1_flip := by
    intro h; have h1 := congrArg (·.cell1.2) h; simp [vertical_1_1, vertical_1_1_flip] at h1
  have hdisj := T.pairwise_disjoint vertical_1_1 hv vertical_1_1_flip hvf hne
  simp only [Finset.disjoint_iff_ne, Domino.cells, vertical_1_1, vertical_1_1_flip,
    Finset.mem_insert, Finset.mem_singleton] at hdisj
  exact hdisj (1, 1) (by left; rfl) (1, 1) (by right; rfl) rfl


-- created on 2026-10-20
