import Mathlib
import Abbrev.Combinatorics.Tiling.DominoTilings
open Finset BigOperators


namespace DominoTilings

def Rectangle (n m : ℕ) : Finset Cell :=
  (Finset.range n ×ˢ Finset.range m).map ⟨fun (x, y) => (x + 1, y + 1), by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    ext <;> omega⟩


end DominoTilings
