import Mathlib
import Theorem.Combinatorics.Tiling.DominoTilings.Part2
open Finset BigOperators


namespace DominoTilings

def vertical_1_1 : Domino where
  cell1 := (1, 1)
  cell2 := (1, 2)
  distinct := by decide
  adjacent := Or.inl ⟨rfl, Or.inl rfl⟩


def horizontal_1_1 : Domino where
  cell1 := (1, 1)
  cell2 := (2, 1)
  distinct := by decide
  adjacent := Or.inr ⟨rfl, Or.inl rfl⟩


def horizontal_1_2 : Domino where
  cell1 := (1, 2)
  cell2 := (2, 2)
  distinct := by decide
  adjacent := Or.inr ⟨rfl, Or.inl rfl⟩

end DominoTilings
