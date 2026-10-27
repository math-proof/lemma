import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part4
open Finset BigOperators


namespace DominoTilings

@[simp] theorem vertical_1_1_cell1 : vertical_1_1.cell1 = (1, 1) := rfl

@[simp] theorem vertical_1_1_cell2 : vertical_1_1.cell2 = (1, 2) := rfl

@[simp] theorem horizontal_1_1_cell1 : horizontal_1_1.cell1 = (1, 1) := rfl

@[simp] theorem horizontal_1_1_cell2 : horizontal_1_1.cell2 = (2, 1) := rfl

@[simp] theorem horizontal_1_2_cell1 : horizontal_1_2.cell1 = (1, 2) := rfl

@[simp] theorem horizontal_1_2_cell2 : horizontal_1_2.cell2 = (2, 2) := rfl

theorem vertical_1_1_cells : vertical_1_1.cells = {(1, 1), (1, 2)} := rfl

end DominoTilings
