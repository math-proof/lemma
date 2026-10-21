import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.Even.AnyTilingEquiv.of.IsFaultfree.DominoTiling
import Lemma.Nat.DominoTilings.reflectTiling3_hasTopVertical_iff_hasBottomVertical
import Lemma.Nat.DominoTilings.reflectTiling3_preserves_TilingEquiv
import Lemma.Nat.DominoTilings.TilingB_eq_reflectTiling3_TilingA
import Lemma.Nat.DominoTilings.reflectTiling3_isFaultfree
import Lemma.Nat.DominoTilings.reflectTiling3_involutive
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
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (hbot : T.hasBottomVerticalInCol 1) :
-- imply
  Even n ∧ ∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingB n hn hn_ge) := by
-- proof
  -- Reflect T to get T' with top vertical
  let T' := reflectTiling3 T -- T' is faultfree
  have hfree' : T'.isFaultfree := _root_.Nat.DominoTilings.reflectTiling3_isFaultfree T hfree -- T' has top vertical in column 1
  have htop' : T'.hasTopVerticalInCol 1 := by
    rwa [_root_.Nat.DominoTilings.reflectTiling3_hasTopVertical_iff_hasBottomVertical] -- Apply classification to T'
  obtain ⟨hn, hn_even, hn_ge, hT'⟩ := Even.AnyTilingEquiv.of.IsFaultfree.DominoTiling n T' hfree' htop'
  constructor
  · exact hn
  ·
    use hn_even, hn_ge -- T' ≃ TilingA n, so T ≃ reflectTiling3 T' ≃ reflectTiling3 (TilingA n) = TilingB n -- TilingEquiv is defined as equality of cell images -- reflectTiling3 preserves TilingEquiv because it's a bijection on cells
    unfold DominoTiling.TilingEquiv at hT'
    unfold DominoTiling.TilingEquiv -- hT' : T'.dominos.image Domino.cells = (TilingA n hn_even hn_ge).dominos.image Domino.cells -- Goal: T.dominos.image Domino.cells = (TilingB n hn_even hn_ge).dominos.image Domino.cells -- T = reflectTiling3 (reflectTiling3 T) = reflectTiling3 T'
    have hT_eq : T = reflectTiling3 T' := (_root_.Nat.DominoTilings.reflectTiling3_involutive T).symm -- TilingB n = reflectTiling3 (TilingA n)
    have hB_eq : TilingB n hn_even hn_ge = reflectTiling3 (TilingA n hn_even hn_ge) :=
      _root_.Nat.DominoTilings.TilingB_eq_reflectTiling3_TilingA n hn_even hn_ge
    rw [hT_eq, hB_eq] -- Now show: (reflectTiling3 T').dominos.image Domino.cells = --           (reflectTiling3 (TilingA n)).dominos.image Domino.cells -- This follows because reflectTiling3 preserves TilingEquiv
    exact _root_.Nat.DominoTilings.reflectTiling3_preserves_TilingEquiv T' (TilingA n hn_even hn_ge) hT'


-- created on 2026-10-20
