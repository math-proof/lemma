import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part3
open Finset BigOperators


namespace DominoTilings

namespace Domino

@[simp]
theorem shiftNat_cell1 (d : Domino) (k : ℕ) : (d.shiftNat k).cell1 = (d.cell1.1 + k, d.cell1.2) := rfl

@[simp]
theorem shiftNat_cell2 (d : Domino) (k : ℕ) : (d.shiftNat k).cell2 = (d.cell2.1 + k, d.cell2.2) := rfl

@[simp]
theorem shiftNeg_cell1 (d : Domino) (k : ℕ) (h1 : d.cell1.1 ≥ k + 1) (h2 : d.cell2.1 ≥ k + 1) :
    (d.shiftNeg k h1 h2).cell1 = (d.cell1.1 - k, d.cell1.2) := rfl

@[simp]
theorem shiftNeg_cell2 (d : Domino) (k : ℕ) (h1 : d.cell1.1 ≥ k + 1) (h2 : d.cell2.1 ≥ k + 1) :
    (d.shiftNeg k h1 h2).cell2 = (d.cell2.1 - k, d.cell2.2) := rfl


end Domino
end DominoTilings
