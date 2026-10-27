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
  (d : Domino)
  (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1)
  (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  (d.shiftNeg k h0 h1).cell2 = (d.cell2.1 - k, d.cell2.2) :=
-- proof
  rfl


-- created on 2026-10-20
