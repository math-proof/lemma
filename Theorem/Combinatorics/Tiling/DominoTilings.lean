import Mathlib
import Def.Combinatorics.Tiling.DominoTilings
open Finset BigOperators


namespace DominoTilings

theorem mem_Rectangle {n m : ℕ} {c : Cell} :
    c ∈ Rectangle n m ↔ c.1 ≥ 1 ∧ c.1 ≤ n ∧ c.2 ≥ 1 ∧ c.2 ≤ m := by
  simp only [Rectangle, Finset.mem_map, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨hx, hy⟩, h⟩
    have : c = (x + 1, y + 1) := h.symm
    simp only [this]
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨c.1 - 1, c.2 - 1, ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · show (c.1 - 1 + 1, c.2 - 1 + 1) = c
      ext <;> omega


end DominoTilings
