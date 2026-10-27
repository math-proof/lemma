import Mathlib
import Theorem.Combinatorics.Tiling.DominoTilings.Part3
open Finset BigOperators


namespace DominoTilings

def vertical_1_1_flip : Domino where
  cell1 := (1, 2)
  cell2 := (1, 1)
  distinct := by decide
  adjacent := Or.inl ⟨rfl, Or.inr rfl⟩

end DominoTilings
