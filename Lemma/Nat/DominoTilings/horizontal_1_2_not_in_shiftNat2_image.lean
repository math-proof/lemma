import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.Cell1Eq1Add.of.Domino
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
  (S : Finset Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  horizontal_1_2 ∉ S.image (fun d => d.shiftNat 2) := by
-- proof
  simp only [Finset.mem_image, not_exists, not_and]
  intro d hd h
  have h1 := congrArg Domino.cell1 h
  simp only [Cell1Eq1Add.of.Domino, horizontal_1_2_cell1, Prod.mk.injEq] at h1
  have hd_pos := (hS d hd).1
  omega


-- created on 2026-10-20
