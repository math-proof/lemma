import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.Cell1Eq1Add.of.Domino
import Lemma.Nat.Cell2Eq1Add.of.Domino
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
  (k : ℕ) :
-- imply
  Function.Injective (fun d : Domino => d.shiftNat k) := by
-- proof
  intro d1 d2 h
  simp only [Domino.ext_iff, Cell1Eq1Add.of.Domino, Cell2Eq1Add.of.Domino, Prod.mk.injEq] at h
  ext <;> omega


-- created on 2026-10-20
