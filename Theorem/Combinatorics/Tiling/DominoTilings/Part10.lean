import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part12
open Finset BigOperators


namespace DominoTilings

theorem reflectDomino3_injective {d1 d2 : Domino}
    (h1a : d1.cell1.2 ≤ 3) (h1b : d1.cell2.2 ≤ 3)
    (h2a : d2.cell1.2 ≤ 3) (h2b : d2.cell2.2 ≤ 3)
    (heq : reflectDomino3 d1 h1a h1b = reflectDomino3 d2 h2a h2b) : d1 = d2 := by
  simp only [reflectDomino3, Domino.mk.injEq, reflectCell3, Prod.mk.injEq] at heq
  ext <;> omega


theorem reflectCell3_mem_Rectangle' {n : ℕ} {c : Cell} (hc : c ∈ Rectangle n 3) :
    reflectCell3 c ∈ Rectangle n 3 := by
  rw [mem_Rectangle] at hc ⊢
  simp only [reflectCell3]
  omega


theorem reflectDomino3_cells {d : Domino} (h1 : d.cell1.2 ≤ 3) (h2 : d.cell2.2 ≤ 3) :
    (reflectDomino3 d h1 h2).cells = d.cells.image reflectCell3 := by
  simp only [Domino.cells, reflectDomino3, Finset.image_insert, Finset.image_singleton]


theorem reflectDomino3_cells_subset {n : ℕ} {d : Domino}
    (hd : d.cells ⊆ Rectangle n 3) (h1 : d.cell1.2 ≤ 3) (h2 : d.cell2.2 ≤ 3) :
    (reflectDomino3 d h1 h2).cells ⊆ Rectangle n 3 := by
  intro c hc
  rw [reflectDomino3_cells] at hc
  simp only [Finset.mem_image] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  exact reflectCell3_mem_Rectangle' (hd hc')


theorem reflectCell3_injective_on_rect {n : ℕ} {c1 c2 : Cell}
    (hc1 : c1 ∈ Rectangle n 3) (hc2 : c2 ∈ Rectangle n 3)
    (heq : reflectCell3 c1 = reflectCell3 c2) : c1 = c2 := by
  rw [mem_Rectangle] at hc1 hc2
  simp only [reflectCell3, Prod.mk.injEq] at heq
  ext <;> omega


theorem reflectCell3_surjective_on_rect {n : ℕ} {c : Cell}
    (hc : c ∈ Rectangle n 3) : ∃ c' ∈ Rectangle n 3, reflectCell3 c' = c := by
  rw [mem_Rectangle] at hc
  use (c.1, 4 - c.2)
  constructor
  · rw [mem_Rectangle]
    simp only
    omega
  · simp only [reflectCell3]
    ext <;> omega


end DominoTilings
