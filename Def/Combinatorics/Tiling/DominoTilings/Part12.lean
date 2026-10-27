import Mathlib
import Theorem.Combinatorics.Tiling.DominoTilings.Part9
open Finset BigOperators


namespace DominoTilings

def reflectDomino3 (d : Domino) (h1 : d.cell1.2 ≤ 3) (h2 : d.cell2.2 ≤ 3) : Domino where
  cell1 := reflectCell3 d.cell1
  cell2 := reflectCell3 d.cell2
  distinct := by
    simp only [reflectCell3, ne_eq, Prod.mk.injEq, not_and]
    intro hcol hsub
    have hdist := d.distinct
    apply hdist
    ext
    · exact hcol
    · exact nat_sub_inj_4 (by omega : d.cell1.2 ≤ 4) (by omega : d.cell2.2 ≤ 4) hsub
  adjacent := by
    simp only [reflectCell3]
    rcases d.adjacent with ⟨hcol, hor⟩ | ⟨hrow, hor⟩
    · left
      constructor
      · exact hcol
      · rcases hor with h | h
        · right; omega
        · left; omega
    · right
      constructor
      · omega
      · exact hor


end DominoTilings
