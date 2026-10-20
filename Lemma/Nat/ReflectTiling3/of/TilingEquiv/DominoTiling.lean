import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (T₁ T₂ : DominoTiling n 3)
  (h : DominoTiling.TilingEquiv T₁ T₂) :
-- imply
  DominoTiling.TilingEquiv (reflectTiling3 T₁) (reflectTiling3 T₂) := by
-- proof
  unfold DominoTiling.TilingEquiv at h
  unfold DominoTiling.TilingEquiv
  -- h : T₁.dominos.image cells = T₂.dominos.image cells
  -- Goal: (reflectTiling3 T₁).dominos.image cells = (reflectTiling3 T₂).dominos.image cells
  -- The key is that (reflectTiling3 T).dominos.image cells transforms each cell set
  -- by applying reflectCell3 to each cell
  simp only [reflectTiling3]
  -- Both sides have the form: (T.dominos.attach.map ...).image Domino.cells
  -- We need to show they're equal given h
  ext S
  simp only [Finset.mem_image, Finset.mem_map, Finset.mem_attach, true_and,
    Subtype.exists, ← Function.Embedding.toFun_eq_coe]
  constructor
  ·
    rintro ⟨d, ⟨d₁, hd₁, rfl⟩, rfl⟩
    -- S = (reflectDomino3 d₁ ...).cells = d₁.cells.image reflectCell3
    rw [reflectDomino3_cells]
    -- d₁.cells ∈ T₁.dominos.image cells
    have h1 : d₁.cells ∈ T₁.dominos.image Domino.cells := Finset.mem_image_of_mem _ hd₁
    rw [h] at h1
    simp only [Finset.mem_image] at h1
    obtain ⟨d₂, hd₂, hcells⟩ := h1
    -- There exists d₂ ∈ T₂.dominos with d₂.cells = d₁.cells
    use reflectDomino3 d₂ (domino_cell1_row_le' (T₂.dominos_in_rect d₂ hd₂))
      (domino_cell2_row_le' (T₂.dominos_in_rect d₂ hd₂))
    constructor
    · exact ⟨d₂, hd₂, rfl⟩
    · rw [reflectDomino3_cells, hcells]
  ·
    rintro ⟨d, ⟨d₂, hd₂, rfl⟩, rfl⟩
    rw [reflectDomino3_cells]
    have h2 : d₂.cells ∈ T₂.dominos.image Domino.cells := Finset.mem_image_of_mem _ hd₂
    rw [← h] at h2
    simp only [Finset.mem_image] at h2
    obtain ⟨d₁, hd₁, hcells⟩ := h2
    use reflectDomino3 d₁ (domino_cell1_row_le' (T₁.dominos_in_rect d₁ hd₁))
      (domino_cell2_row_le' (T₁.dominos_in_rect d₁ hd₁))
    constructor
    · exact ⟨d₁, hd₁, rfl⟩
    · rw [reflectDomino3_cells, hcells]


-- created on 2026-10-20
