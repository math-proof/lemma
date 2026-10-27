import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


/-- Local copy of sympy private `reflectDomino3` (same body via public `reflectCell3`). -/
private def reflectDomino3 (d : Domino) (h1 : d.cell1.2 ≤ 3) (h2 : d.cell2.2 ≤ 3) : Domino where
  cell1 := reflectCell3 d.cell1
  cell2 := reflectCell3 d.cell2
  distinct := by
    simp only [reflectCell3, ne_eq, Prod.mk.injEq, not_and]
    intro hcol hsub
    exact d.distinct (Prod.ext hcol (by omega))
  adjacent := by
    simp only [reflectCell3]
    obtain ⟨hcol, hor⟩ | ⟨hrow, hor⟩ := d.adjacent
    ·
      left
      constructor
      · exact hcol
      ·
        obtain h | h := hor
        ·
          right
          omega
        ·
          left
          omega
    ·
      right
      constructor
      · omega
      · exact hor

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  {d : Domino}
  (h0 : d.cell1.2 ≤ 3)
  (h1 : d.cell2.2 ≤ 3) :
-- imply
  (reflectDomino3 d h0 h1).minCol = d.minCol := by
-- proof
  simp only [Domino.minCol, reflectDomino3, reflectCell3]


-- created on 2026-10-20
