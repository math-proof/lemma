import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.EqShiftNat.of.Ge1Add1.Ge1Add1.Domino
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
  (d : Domino)
  (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1)
  (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  ((d.shiftNeg k h0 h1).shiftNat k).cells = d.cells := by
-- proof
  rw [EqShiftNat.of.Ge1Add1.Ge1Add1.Domino]


-- created on 2026-10-20
