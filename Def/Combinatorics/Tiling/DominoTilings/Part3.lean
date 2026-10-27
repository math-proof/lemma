import Mathlib
import Instance.Combinatorics.Tiling.DominoTilings
open Finset BigOperators


namespace DominoTilings

namespace Domino

def minCol (d : Domino) : ℕ := min d.cell1.1 d.cell2.1


def maxCol (d : Domino) : ℕ := max d.cell1.1 d.cell2.1


def shiftNat (d : Domino) (k : ℕ) : Domino where
  cell1 := (d.cell1.1 + k, d.cell1.2)
  cell2 := (d.cell2.1 + k, d.cell2.2)
  distinct := by
    intro h
    simp only [Prod.mk.injEq] at h
    exact d.distinct (Prod.ext (by omega) h.2)
  adjacent := by
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · left
      constructor
      · simp only [hcol]
      · rcases hrow with h | h <;> [left; right] <;> omega
    · right
      constructor
      · exact hrow
      · rcases hcol with h | h <;> [left; right] <;> omega


def shiftNeg (d : Domino) (k : ℕ) (h1 : d.cell1.1 ≥ k + 1) (h2 : d.cell2.1 ≥ k + 1) : Domino where
  cell1 := (d.cell1.1 - k, d.cell1.2)
  cell2 := (d.cell2.1 - k, d.cell2.2)
  distinct := by
    intro h
    simp only [Prod.mk.injEq] at h
    have hdist := d.distinct
    apply hdist
    ext
    · omega
    · exact h.2
  adjacent := by
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · left
      constructor
      · omega
      · rcases hrow with h | h <;> [left; right] <;> omega
    · right
      constructor
      · exact hrow
      · rcases hcol with h | h <;> [left; right] <;> omega

end Domino
end DominoTilings
