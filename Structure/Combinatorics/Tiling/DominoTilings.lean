import Mathlib
import Theorem.Combinatorics.Tiling.DominoTilings
open Finset BigOperators


namespace DominoTilings

@[ext]
structure Domino where
  
  cell1 : Cell
  
  cell2 : Cell
  
  distinct : cell1 ≠ cell2
  
  adjacent : (cell1.1 = cell2.1 ∧ (cell1.2 + 1 = cell2.2 ∨ cell2.2 + 1 = cell1.2)) ∨
             (cell1.2 = cell2.2 ∧ (cell1.1 + 1 = cell2.1 ∨ cell2.1 + 1 = cell1.1))
  deriving DecidableEq

end DominoTilings
