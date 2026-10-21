import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings.TilingB_eq_reflectTiling3_TilingA
import Lemma.Nat.DominoTilings.reflectTiling3_isFaultfree
import Lemma.Nat.DominoTilings.TilingA_isFaultfree
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
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  (TilingB n hn hn_ge).isFaultfree := by
-- proof
  rw [_root_.Nat.DominoTilings.TilingB_eq_reflectTiling3_TilingA]
  exact _root_.Nat.DominoTilings.reflectTiling3_isFaultfree (TilingA n hn hn_ge) (_root_.Nat.DominoTilings.TilingA_isFaultfree n hn hn_ge)


-- created on 2026-10-20
