import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
open DominoTilings
open DominoTilings.Domino
open DominoTilings.DominoTiling


section
-- ac-theorems


open Finset BigOperators

namespace DominoTilings

namespace Domino


end Domino

@[simp] lemma vertical_1_1_isVertical : vertical_1_1.isVertical := rfl
@[simp] lemma horizontal_1_1_isHorizontal : horizontal_1_1.isHorizontal := rfl
@[simp] lemma horizontal_1_2_isHorizontal : horizontal_1_2.isHorizontal := rfl

namespace DominoTiling


end DominoTiling


/-- The rectangle R_{n,m} has exactly n * m cells. -/
lemma card_Rectangle (n m : ℕ) : (Rectangle n m).card = n * m := by
  simp [Rectangle, Finset.card_map, Finset.card_product]

namespace Domino


/-- Shifting left then right returns the original domino. -/
lemma shiftNat_shiftNeg (d : Domino) (k : ℕ) (h1 : d.cell1.1 ≥ k + 1) (h2 : d.cell2.1 ≥ k + 1) :
    (d.shiftNeg k h1 h2).shiftNat k = d := by
  simp only [shiftNat, shiftNeg]
  ext <;> simp <;> omega
/-- Each domino covers exactly 2 cells. -/
@[simp]
lemma card_cells (d : Domino) : d.cells.card = 2 := by
  simp [cells, Finset.card_pair d.distinct]

/-- Every domino is either horizontal or vertical. -/
lemma isHorizontal_or_isVertical (d : Domino) : d.isHorizontal ∨ d.isVertical := by
  rcases d.adjacent with ⟨hcol, _⟩ | ⟨hrow, _⟩
  · exact Or.inr hcol
  · exact Or.inl hrow

/-- A domino cannot be both horizontal and vertical. -/
lemma not_isHorizontal_and_isVertical (d : Domino) : ¬(d.isHorizontal ∧ d.isVertical) := by
  intro ⟨hH, hV⟩
  exact d.distinct (Prod.ext hV hH)

/-- A domino is horizontal iff it's not vertical. -/
lemma isHorizontal_iff_not_isVertical (d : Domino) : d.isHorizontal ↔ ¬d.isVertical := by
  constructor
  · intro hH hV
    exact d.not_isHorizontal_and_isVertical ⟨hH, hV⟩
  · intro hNV
    rcases d.isHorizontal_or_isVertical with hH | hV
    · exact hH
    · exact absurd hV hNV

/-- A domino is vertical iff it's not horizontal. -/
lemma isVertical_iff_not_isHorizontal (d : Domino) : d.isVertical ↔ ¬d.isHorizontal := by
  constructor
  · intro hV hH
    exact d.not_isHorizontal_and_isVertical ⟨hH, hV⟩
  · intro hNH
    rcases d.isHorizontal_or_isVertical with hH | hV
    · exact absurd hH hNH
    · exact hV

/-- Every domino is either horizontal or vertical (exclusive or). -/
lemma isHorizontal_xor_isVertical (d : Domino) : Xor d.isHorizontal d.isVertical := by
  rcases d.isHorizontal_or_isVertical with hH | hV
  · exact Or.inl ⟨hH, fun hV => d.not_isHorizontal_and_isVertical ⟨hH, hV⟩⟩
  · exact Or.inr ⟨hV, fun hH => d.not_isHorizontal_and_isVertical ⟨hH, hV⟩⟩

/-- Shifting right then left returns the original domino (when original has positive columns). -/
lemma shiftNeg_shiftNat (d : Domino) (k : ℕ) (hc1 : d.cell1.1 ≥ 1) (hc2 : d.cell2.1 ≥ 1) :
    (d.shiftNat k).shiftNeg k (by simp [shiftNat]; omega) (by simp [shiftNat]; omega) = d := by
  simp only [shiftNat, shiftNeg]
  ext <;> simp

/-- Cells are preserved through shift-unshift: (d.shiftNeg k ...).shiftNat k has the same cells as d.
    This is a corollary of shiftNat_shiftNeg and is useful for proving TilingEquiv. -/

lemma shiftNat_shiftNeg_cells (d : Domino) (k : ℕ) (h1 : d.cell1.1 ≥ k + 1) (h2 : d.cell2.1 ≥ k + 1) :
    ((d.shiftNeg k h1 h2).shiftNat k).cells = d.cells := by
  rw [shiftNat_shiftNeg]

/-- shiftNat is injective. -/
lemma shiftNat_injective (k : ℕ) : Function.Injective (fun d : Domino => d.shiftNat k) := by
  intro d1 d2 h
  simp only [Domino.ext_iff, shiftNat_cell1, shiftNat_cell2, Prod.mk.injEq] at h
  ext <;> omega

/-- shiftNeg is injective (when both dominos have sufficient column coordinates). -/
lemma shiftNeg_injective {d1 d2 : Domino} {k : ℕ}
    (h1_1 : d1.cell1.1 ≥ k + 1) (h1_2 : d1.cell2.1 ≥ k + 1)
    (h2_1 : d2.cell1.1 ≥ k + 1) (h2_2 : d2.cell2.1 ≥ k + 1)
    (heq : d1.shiftNeg k h1_1 h1_2 = d2.shiftNeg k h2_1 h2_2) : d1 = d2 := by
  have h1 := congrArg (·.cell1) heq
  have h2 := congrArg (·.cell2) heq
  unfold shiftNeg at h1 h2
  simp only [Prod.mk.injEq] at h1 h2
  have hc1_1 : d1.cell1.1 = d2.cell1.1 := by omega
  have hc2_1 : d1.cell2.1 = d2.cell2.1 := by omega
  cases d1
  cases d2
  simp only [Domino.mk.injEq]
  simp only at hc1_1 hc2_1 h1 h2
  constructor <;> ext <;> simp_all

/-- A shifted domino has minCol at least k+1 when original has positive columns. -/
lemma shiftNat_minCol_ge (d : Domino) (k : ℕ) (hc1 : d.cell1.1 ≥ 1) (hc2 : d.cell2.1 ≥ 1) :
    (d.shiftNat k).minCol ≥ k + 1 := by
  simp only [minCol, shiftNat_cell1, shiftNat_cell2, ge_iff_le, le_min_iff]
  omega

/-- Vertical dominos remain vertical after shifting. -/
lemma shiftNat_isVertical (d : Domino) (k : ℕ) (h : d.isVertical) :
    (d.shiftNat k).isVertical := by
  simp only [isVertical, shiftNat_cell1, shiftNat_cell2] at h ⊢
  omega

/-- Horizontal dominos remain horizontal after shifting. -/
lemma shiftNat_isHorizontal (d : Domino) (k : ℕ) (h : d.isHorizontal) :
    (d.shiftNat k).isHorizontal := by
  simp only [isHorizontal, shiftNat_cell1, shiftNat_cell2] at h ⊢
  exact h

end Domino

lemma horizontal_1_1_cells : horizontal_1_1.cells = {(1, 1), (2, 1)} := rfl

lemma horizontal_1_2_cells : horizontal_1_2.cells = {(1, 2), (2, 2)} := rfl

/-- The vertical domino is not equal to horizontal_1_1. -/
lemma vertical_1_1_ne_horizontal_1_1 : vertical_1_1 ≠ horizontal_1_1 := by
  intro h
  have := congrArg Domino.cell2 h
  simp at this

/-- The vertical domino is not equal to horizontal_1_2. -/
lemma vertical_1_1_ne_horizontal_1_2 : vertical_1_1 ≠ horizontal_1_2 := by
  intro h
  have := congrArg Domino.cell1 h
  simp at this

/-- horizontal_1_1 is not equal to horizontal_1_2. -/
lemma horizontal_1_1_ne_horizontal_1_2 : horizontal_1_1 ≠ horizontal_1_2 := by
  intro h
  have := congrArg Domino.cell1 h
  simp at this


@[simp] lemma vertical_1_1_flip_cell1 : vertical_1_1_flip.cell1 = (1, 2) := rfl
@[simp] lemma vertical_1_1_flip_cell2 : vertical_1_1_flip.cell2 = (1, 1) := rfl

lemma vertical_1_1_flip_cells : vertical_1_1_flip.cells = {(1, 2), (1, 1)} := rfl

lemma vertical_1_1_flip_cells_eq : vertical_1_1_flip.cells = vertical_1_1.cells := by
  simp only [vertical_1_1_flip_cells, vertical_1_1_cells, Finset.pair_comm]

lemma vertical_1_1_ne_vertical_1_1_flip : vertical_1_1 ≠ vertical_1_1_flip := by
  intro h
  have := congrArg Domino.cell1 h
  simp at this

/-- If a domino has the same cells as vertical_1_1, it is either vertical_1_1 or vertical_1_1_flip. -/
lemma eq_vertical_1_1_of_cells_eq (d : Domino) (h : d.cells = vertical_1_1.cells) :
    d = vertical_1_1 ∨ d = vertical_1_1_flip := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
    have hmem : d.cell1 ∈ ({d.cell1, d.cell2} : Finset Cell) := Finset.mem_insert_self _ _
    rw [h] at hmem
    exact hmem
  have h2 : d.cell2 ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
    have hmem : d.cell2 ∈ ({d.cell1, d.cell2} : Finset Cell) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [h] at hmem
    exact hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with hc1_11 | hc1_12 <;> rcases h2 with hc2_11 | hc2_12
  · have : d.cell1 = d.cell2 := by simp only [hc1_11, hc2_11]
    exact absurd this d.distinct
  · left; ext <;> simp only [vertical_1_1, hc1_11, hc2_12]
  · right; ext <;> simp only [vertical_1_1_flip, hc1_12, hc2_11]
  · have : d.cell1 = d.cell2 := by simp only [hc1_12, hc2_12]
    exact absurd this d.distinct

/-- vertical_1_1 is not in the image of shiftNat by 1 for dominos with positive columns. -/
lemma vertical_1_1_not_in_shiftNat1_image (S : Finset Domino)
    (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
    vertical_1_1 ∉ S.image (fun d => d.shiftNat 1) := by
  simp only [Finset.mem_image, not_exists, not_and]
  intro d hd h
  have h1 := congrArg Domino.cell1 h
  simp only [Domino.shiftNat_cell1, vertical_1_1_cell1, Prod.mk.injEq] at h1
  have hd_pos := (hS d hd).1
  omega

/-- horizontal_1_1 is not in the image of shiftNat by 2 for dominos with positive columns. -/
lemma horizontal_1_1_not_in_shiftNat2_image (S : Finset Domino)
    (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
    horizontal_1_1 ∉ S.image (fun d => d.shiftNat 2) := by
  simp only [Finset.mem_image, not_exists, not_and]
  intro d hd h
  have h1 := congrArg Domino.cell1 h
  simp only [Domino.shiftNat_cell1, horizontal_1_1_cell1, Prod.mk.injEq] at h1
  have hd_pos := (hS d hd).1
  omega

/-- horizontal_1_2 is not in the image of shiftNat by 2 for dominos with positive columns. -/
lemma horizontal_1_2_not_in_shiftNat2_image (S : Finset Domino)
    (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
    horizontal_1_2 ∉ S.image (fun d => d.shiftNat 2) := by
  simp only [Finset.mem_image, not_exists, not_and]
  intro d hd h
  have h1 := congrArg Domino.cell1 h
  simp only [Domino.shiftNat_cell1, horizontal_1_2_cell1, Prod.mk.injEq] at h1
  have hd_pos := (hS d hd).1
  omega

/-- vertical_1_1 is not in the image of shiftNat by 2 for dominos with positive columns. -/
lemma vertical_1_1_not_in_shiftNat2_image (S : Finset Domino)
    (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
    vertical_1_1 ∉ S.image (fun d => d.shiftNat 2) := by
  simp only [Finset.mem_image, not_exists, not_and]
  intro d hd h
  have h1 := congrArg Domino.cell1 h
  simp only [Domino.shiftNat_cell1, vertical_1_1_cell1, Prod.mk.injEq] at h1
  have hd_pos := (hS d hd).1
  omega

namespace DominoTiling

variable {n m : ℕ}

/-- Dominos in a tiling have cells with positive row coordinates. -/
lemma domino_cells_row_ge_one (T : DominoTiling n m) (d : Domino) (hd : d ∈ T.dominos) :
    d.cell1.2 ≥ 1 ∧ d.cell2.2 ≥ 1 := by
  have h := T.dominos_in_rect d hd
  have hc1 : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
  have hc2 : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h1 := h hc1
  have h2 := h hc2
  rw [mem_Rectangle] at h1 h2
  exact ⟨h1.2.2.1, h2.2.2.1⟩

/-- The cardinality of the rectangle equals twice the number of dominos in any tiling. -/
lemma card_eq_twice_dominos (T : DominoTiling n m) :
    (Rectangle n m).card = 2 * T.dominos.card := by
  rw [← T.covers_all]
  rw [Finset.card_biUnion]
  · have h : ∑ d ∈ T.dominos, d.cells.card = ∑ _d ∈ T.dominos, 2 := by
      apply Finset.sum_congr rfl
      intro d _
      exact Domino.card_cells d
    rw [h]
    simp [mul_comm]
  · intro d₁ hd₁ d₂ hd₂ hne
    exact T.pairwise_disjoint d₁ hd₁ d₂ hd₂ hne

/-- Every cell in the rectangle is covered by some domino in the tiling. -/
lemma cell_covered (T : DominoTiling n m) (c : Cell) (hc : c ∈ Rectangle n m) :
    ∃ d ∈ T.dominos, c ∈ d.cells := by
  rw [← T.covers_all] at hc
  simp only [Finset.mem_biUnion] at hc
  exact hc

/-- If a cell is covered by two dominos in a tiling, they must be the same domino.
    This follows from the pairwise disjointness of dominos in a tiling. -/

lemma cell_covered_unique (T : DominoTiling n m) (c : Cell)
    (d₁ d₂ : Domino) (hd₁ : d₁ ∈ T.dominos) (hd₂ : d₂ ∈ T.dominos)
    (hc₁ : c ∈ d₁.cells) (hc₂ : c ∈ d₂.cells) : d₁ = d₂ := by
  by_contra hne
  have hdisj := T.pairwise_disjoint d₁ hd₁ d₂ hd₂ hne
  rw [Finset.disjoint_iff_ne] at hdisj
  exact hdisj c hc₁ c hc₂ rfl

/-- TilingEquiv is reflexive. -/
lemma tilingEquiv_refl (T : DominoTiling n m) : TilingEquiv T T := rfl

/-- TilingEquiv is symmetric. -/
lemma tilingEquiv_symm {T₁ T₂ : DominoTiling n m} (h : TilingEquiv T₁ T₂) :
    TilingEquiv T₂ T₁ := h.symm

/-- TilingEquiv is transitive. -/
lemma tilingEquiv_trans {T₁ T₂ T₃ : DominoTiling n m}
    (h₁ : TilingEquiv T₁ T₂) (h₂ : TilingEquiv T₂ T₃) : TilingEquiv T₁ T₃ :=
  h₁.trans h₂

/-- Helper lemma: replacing an element v with w in a finset preserves the image
    when f(v) = f(w). This is the key lemma for proving TilingEquiv is preserved
    when replacing a domino with another domino covering the same cells. -/

lemma image_erase_insert_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (v w : α) (f : α → β) (hv : v ∈ S) (hf : f v = f w) :
    (insert w (S.erase v)).image f = S.image f := by
  ext b
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨a, (rfl | ⟨hne, ha⟩), hab⟩
    · refine ⟨v, hv, ?_⟩; rw [hf]; exact hab
    · exact ⟨a, ha, hab⟩
  · rintro ⟨a, ha, rfl⟩
    by_cases h : a = v
    · subst h; exact ⟨w, Or.inl rfl, hf.symm⟩
    · exact ⟨a, Or.inr ⟨h, ha⟩, rfl⟩

/-- prependVertical followed by restrictAfterVertical is the identity. -/
lemma restrictAfterVertical_prependVertical (T : DominoTiling n 2) :
    restrictAfterVertical (prependVertical T) (by simp [prependVertical, vertical_1_1]) = T := by
  cases T with
  | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    unfold prependVertical restrictAfterVertical
    congr 1
    ext d
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · -- Forward: d is in the result of restrictAfterVertical (prependVertical T)
      intro hd
      obtain ⟨d', hd'_erase, hd'_eq⟩ := hd
      have hd'_ne : d' ≠ vertical_1_1 := (Finset.mem_erase.mp hd'_erase).1
      have hd'_mem : d' ∈ insert vertical_1_1 (dominos.image (fun d => d.shiftNat 1)) :=
        Finset.mem_of_mem_erase hd'_erase
      rw [Finset.mem_insert] at hd'_mem
      rcases hd'_mem with rfl | hd'_in_image
      · exact absurd rfl hd'_ne
      · simp only [Finset.mem_image] at hd'_in_image
        obtain ⟨d'', hd''_mem, hd''_eq⟩ := hd'_in_image
        have hcols := domino_cells_col_ge_one
          ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d'' hd''_mem
        subst hd''_eq
        rw [← hd'_eq]
        -- Show (d''.shiftNat 1).shiftNeg 1 ... = d'' by extensionality
        have h_eq : (d''.shiftNat 1).shiftNeg 1
            (domino_col_ge_two_of_ne_vertical (prependVertical ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩)
              (by simp [prependVertical, vertical_1_1])
              (d''.shiftNat 1)
              (Finset.mem_of_mem_erase hd'_erase)
              hd'_ne).1
            (domino_col_ge_two_of_ne_vertical (prependVertical ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩)
              (by simp [prependVertical, vertical_1_1])
              (d''.shiftNat 1)
              (Finset.mem_of_mem_erase hd'_erase)
              hd'_ne).2
            = d'' := by
          apply Domino.ext
          · simp only [Domino.shiftNeg, Domino.shiftNat]
            simp only [Nat.add_sub_cancel]
          · simp only [Domino.shiftNeg, Domino.shiftNat]
            simp only [Nat.add_sub_cancel]
        rw [h_eq]
        exact hd''_mem
    · -- Backward: d ∈ dominos → d is in the result
      intro hd
      have hcols := domino_cells_col_ge_one
        ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d hd
      have hne : d.shiftNat 1 ≠ vertical_1_1 := by
        intro h
        have h1 := congrArg (·.cell1.1) h
        simp [Domino.shiftNat, vertical_1_1] at h1
        omega
      have hmem : d.shiftNat 1 ∈ dominos.image (fun d => d.shiftNat 1) :=
        Finset.mem_image_of_mem _ hd
      have hmem' : d.shiftNat 1 ∈ insert vertical_1_1 (dominos.image (fun d => d.shiftNat 1)) :=
        Finset.mem_insert_of_mem hmem
      have hmem'' : d.shiftNat 1 ∈ (insert vertical_1_1 (dominos.image (fun d => d.shiftNat 1))).erase vertical_1_1 :=
        Finset.mem_erase.mpr ⟨hne, hmem'⟩
      use d.shiftNat 1, hmem''
      exact Domino.shiftNeg_shiftNat d 1 hcols.1 hcols.2

/-- restrictAfterVertical followed by prependVertical is the identity
    (when the tiling starts with vertical_1_1). -/

lemma prependVertical_restrictAfterVertical (T : DominoTiling (n + 1) 2)
    (hv : vertical_1_1 ∈ T.dominos) :
    prependVertical (restrictAfterVertical T hv) = T := by
  cases T with
  | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    unfold prependVertical restrictAfterVertical
    congr 1
    ext d
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · intro hd
      rcases hd with rfl | ⟨d', hd'_mem, hd'_eq⟩
      · exact hv
      · obtain ⟨d'', hd''_erase, hd''_eq⟩ := hd'_mem
        have hd''_in := Finset.mem_of_mem_erase hd''_erase
        have hd''_ne := (Finset.mem_erase.mp hd''_erase).1
        have hcols := domino_col_ge_two_of_ne_vertical
          ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ hv d'' hd''_in hd''_ne
        -- d' = d''.shiftNeg 1 ..., d = d'.shiftNat 1
        -- So d = (d''.shiftNeg 1 ...).shiftNat 1 = d''
        rw [← hd'_eq, ← hd''_eq]
        rw [Domino.shiftNat_shiftNeg]
        exact hd''_in
    · intro hd
      by_cases hne : d = vertical_1_1
      · left; exact hne
      · right
        have hd_erase : d ∈ dominos.erase vertical_1_1 := Finset.mem_erase.mpr ⟨hne, hd⟩
        have hcols := domino_col_ge_two_of_ne_vertical
          ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ hv d hd hne
        use d.shiftNeg 1 hcols.1 hcols.2
        constructor
        · use d, hd_erase
        · exact Domino.shiftNat_shiftNeg d 1 hcols.1 hcols.2

/-- prependHorizontalPair followed by restrictAfterHorizontalPair is the identity. -/
lemma restrictAfterHorizontalPair_prependHorizontalPair (T : DominoTiling n 2) :
    restrictAfterHorizontalPair (prependHorizontalPair T)
      (by simp [prependHorizontalPair, horizontal_1_1])
      (by simp [prependHorizontalPair, horizontal_1_2]) = T := by
  cases T with
  | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    unfold prependHorizontalPair restrictAfterHorizontalPair
    congr 1
    ext d
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · -- Forward: d is in the result of restrictAfterHorizontalPair (prependHorizontalPair T)
      intro hd
      obtain ⟨d', hd'_erase, hd'_eq⟩ := hd
      -- d' is in ((insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2)))).erase horizontal_1_1).erase horizontal_1_2
      have hd'_ne1 : d' ≠ horizontal_1_1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hd'_erase)).1
      have hd'_ne2 : d' ≠ horizontal_1_2 := (Finset.mem_erase.mp hd'_erase).1
      have hd'_mem : d' ∈ insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2))) :=
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd'_erase)
      rw [Finset.mem_insert] at hd'_mem
      rcases hd'_mem with rfl | hd'_mem'
      · exact absurd rfl hd'_ne1
      · rw [Finset.mem_insert] at hd'_mem'
        rcases hd'_mem' with rfl | hd'_in_image
        · exact absurd rfl hd'_ne2
        · simp only [Finset.mem_image] at hd'_in_image
          obtain ⟨d'', hd''_mem, hd''_eq⟩ := hd'_in_image
          have hcols := domino_cells_col_ge_one
            ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d'' hd''_mem
          subst hd''_eq
          rw [← hd'_eq]
          -- Show (d''.shiftNat 2).shiftNeg 2 ... = d''
          have h_eq : (d''.shiftNat 2).shiftNeg 2
              (other_dominos_col_ge_3 (prependHorizontalPair ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩)
                (by simp [prependHorizontalPair, horizontal_1_1])
                (by simp [prependHorizontalPair, horizontal_1_2])
                (d''.shiftNat 2)
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd'_erase))
                hd'_ne1 hd'_ne2).1
              (other_dominos_col_ge_3 (prependHorizontalPair ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩)
                (by simp [prependHorizontalPair, horizontal_1_1])
                (by simp [prependHorizontalPair, horizontal_1_2])
                (d''.shiftNat 2)
                (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd'_erase))
                hd'_ne1 hd'_ne2).2
              = d'' := by
            apply Domino.ext
            · simp only [Domino.shiftNeg, Domino.shiftNat]
              simp only [Nat.add_sub_cancel]
            · simp only [Domino.shiftNeg, Domino.shiftNat]
              simp only [Nat.add_sub_cancel]
          rw [h_eq]
          exact hd''_mem
    · -- Backward: d ∈ dominos → d is in the result
      intro hd
      have hcols := domino_cells_col_ge_one
        ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d hd
      have hne1 : d.shiftNat 2 ≠ horizontal_1_1 := by
        intro h
        have h1 := congrArg (·.cell1.1) h
        simp [Domino.shiftNat, horizontal_1_1] at h1
      have hne2 : d.shiftNat 2 ≠ horizontal_1_2 := by
        intro h
        have h1 := congrArg (·.cell1.1) h
        simp [Domino.shiftNat, horizontal_1_2] at h1
      have hmem : d.shiftNat 2 ∈ dominos.image (fun d => d.shiftNat 2) :=
        Finset.mem_image_of_mem _ hd
      have hmem' : d.shiftNat 2 ∈ insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2)) :=
        Finset.mem_insert_of_mem hmem
      have hmem'' : d.shiftNat 2 ∈ insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2))) :=
        Finset.mem_insert_of_mem hmem'
      have hmem1 : d.shiftNat 2 ∈ (insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2)))).erase horizontal_1_1 :=
        Finset.mem_erase.mpr ⟨hne1, hmem''⟩
      have hmem2 : d.shiftNat 2 ∈ ((insert horizontal_1_1 (insert horizontal_1_2 (dominos.image (fun d => d.shiftNat 2)))).erase horizontal_1_1).erase horizontal_1_2 :=
        Finset.mem_erase.mpr ⟨hne2, hmem1⟩
      use d.shiftNat 2, hmem2
      exact Domino.shiftNeg_shiftNat d 2 hcols.1 hcols.2

/-- restrictAfterHorizontalPair followed by prependHorizontalPair is the identity
    (when the tiling starts with horizontal_1_1 and horizontal_1_2). -/

lemma prependHorizontalPair_restrictAfterHorizontalPair (T : DominoTiling (n + 2) 2)
    (hh1 : horizontal_1_1 ∈ T.dominos) (hh2 : horizontal_1_2 ∈ T.dominos) :
    prependHorizontalPair (restrictAfterHorizontalPair T hh1 hh2) = T := by
  cases T with
  | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    unfold prependHorizontalPair restrictAfterHorizontalPair
    congr 1
    ext d
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · intro hd
      rcases hd with rfl | rfl | ⟨d', hd'_mem, hd'_eq⟩
      · exact hh1
      · exact hh2
      · obtain ⟨d'', hd''_erase, hd''_eq⟩ := hd'_mem
        have hd''_in := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd''_erase)
        have hd''_ne1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hd''_erase)).1
        have hd''_ne2 := (Finset.mem_erase.mp hd''_erase).1
        have hcols := other_dominos_col_ge_3
          ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ hh1 hh2 d'' hd''_in hd''_ne1 hd''_ne2
        rw [← hd'_eq, ← hd''_eq]
        rw [Domino.shiftNat_shiftNeg]
        exact hd''_in
    · intro hd
      by_cases hne1 : d = horizontal_1_1
      · left; exact hne1
      · by_cases hne2 : d = horizontal_1_2
        · right; left; exact hne2
        · right; right
          have hd_erase : d ∈ (dominos.erase horizontal_1_1).erase horizontal_1_2 := 
            Finset.mem_erase.mpr ⟨hne2, Finset.mem_erase.mpr ⟨hne1, hd⟩⟩
          have hcols := other_dominos_col_ge_3
            ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ hh1 hh2 d hd hne1 hne2
          use d.shiftNeg 2 (by omega) (by omega)
          constructor
          · use d, hd_erase
          · exact Domino.shiftNat_shiftNeg d 2 (by omega) (by omega)

/-- restrictAfterVerticalGen with vertical_1_1 equals restrictAfterVertical. -/
lemma restrictAfterVerticalGen_eq_restrictAfterVertical (T : DominoTiling (n + 1) 2)
    (hv : vertical_1_1 ∈ T.dominos) :
    restrictAfterVerticalGen T vertical_1_1 hv rfl = restrictAfterVertical T hv := by
  -- The two functions produce the same result because they use the same
  -- erase and shift operations, just with different proof terms
  rfl

lemma vertical_1_1_or_flip_of_hasVerticalFirstColumn (T : DominoTiling (n + 2) 2)
    (hvert : hasVerticalFirstColumn T) :
    vertical_1_1 ∈ T.dominos ∨ vertical_1_1_flip ∈ T.dominos := by
  obtain ⟨d, hd_mem, hd_cells⟩ := hvert
  have hd_eq := eq_vertical_1_1_of_cells_eq d (by rw [hd_cells]; rfl)
  rcases hd_eq with rfl | rfl
  · left; exact hd_mem
  · right; exact hd_mem

/-- If vertical_1_1 is in a tiling, then vertical_1_1_flip is not (by disjointness). -/
lemma vertical_1_1_flip_not_mem_of_vertical_1_1_mem (T : DominoTiling n m)
    (hv : vertical_1_1 ∈ T.dominos) : vertical_1_1_flip ∉ T.dominos := by
  intro hvf
  have hne : vertical_1_1 ≠ vertical_1_1_flip := by
    intro h; have h1 := congrArg (·.cell1.2) h; simp [vertical_1_1, vertical_1_1_flip] at h1
  have hdisj := T.pairwise_disjoint vertical_1_1 hv vertical_1_1_flip hvf hne
  simp only [Finset.disjoint_iff_ne, Domino.cells, vertical_1_1, vertical_1_1_flip,
    Finset.mem_insert, Finset.mem_singleton] at hdisj
  have h := hdisj (1, 1) (by left; rfl) (1, 1) (by right; rfl)
  exact h rfl

/-- If vertical_1_1 is in a tiling with a vertical first column, then Classical.choose
    picks vertical_1_1 (since it's the unique witness). -/

lemma classical_choose_hasVerticalFirstColumn_eq_vertical_1_1 (T : DominoTiling (n + 2) 2)
    (hv_mem : vertical_1_1 ∈ T.dominos) (hv : hasVerticalFirstColumn T) :
    Classical.choose hv = vertical_1_1 := by
  have hspec := Classical.choose_spec hv
  -- The chosen domino has cells = vertical_1_1.cells, so it's either vertical_1_1 or vertical_1_1_flip
  rcases eq_vertical_1_1_of_cells_eq _ hspec.2 with heq | heq
  · exact heq
  · -- If it were vertical_1_1_flip, then vertical_1_1_flip ∈ T.dominos
    -- But vertical_1_1 ∈ T.dominos, so by disjointness, vertical_1_1_flip ∉ T.dominos
    exfalso
    rw [heq] at hspec
    exact vertical_1_1_flip_not_mem_of_vertical_1_1_mem T hv_mem hspec.1

/-- In `prependHorizontalPair T`, the only domino with cells `{(1,1), (2,1)}` is `horizontal_1_1`. -/
lemma horizontal_1_1_unique_in_prependHorizontalPair (T : DominoTiling n 2) (d : Domino)
    (hd : d ∈ (prependHorizontalPair T).dominos)
    (hd_cells : d.cells = ({(1, 1), (2, 1)} : Finset Cell)) :
    d = horizontal_1_1 := by
  simp only [prependHorizontalPair, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | rfl | ⟨d', _, rfl⟩
  · rfl
  · -- d = horizontal_1_2, but horizontal_1_2.cells = {(1,2), (2,2)} ≠ {(1,1), (2,1)}
    simp only [Domino.cells, horizontal_1_2] at hd_cells
    have h : ((1, 2) : Cell) ∈ ({(1, 1), (2, 1)} : Finset Cell) := by
      rw [← hd_cells]; exact Finset.mem_insert_self _ _
    simp at h
  · -- d = d'.shiftNat 2, but shifted dominos have column ≥ 3
    have hcols := domino_cells_col_ge_one T d' (by assumption)
    simp only [Domino.cells, Domino.shiftNat_cell1, Domino.shiftNat_cell2] at hd_cells
    have h : (d'.cell1.1 + 2, d'.cell1.2) ∈ ({(1, 1), (2, 1)} : Finset Cell) := by
      rw [← hd_cells]; exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- In `prependHorizontalPair T`, the only domino with cells `{(1,2), (2,2)}` is `horizontal_1_2`. -/
lemma horizontal_1_2_unique_in_prependHorizontalPair (T : DominoTiling n 2) (d : Domino)
    (hd : d ∈ (prependHorizontalPair T).dominos)
    (hd_cells : d.cells = ({(1, 2), (2, 2)} : Finset Cell)) :
    d = horizontal_1_2 := by
  simp only [prependHorizontalPair, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | rfl | ⟨d', _, rfl⟩
  · -- d = horizontal_1_1, but horizontal_1_1.cells = {(1,1), (2,1)} ≠ {(1,2), (2,2)}
    simp only [Domino.cells, horizontal_1_1] at hd_cells
    have h : ((1, 1) : Cell) ∈ ({(1, 2), (2, 2)} : Finset Cell) := by
      rw [← hd_cells]; exact Finset.mem_insert_self _ _
    simp at h
  · rfl
  · -- d = d'.shiftNat 2, but shifted dominos have column ≥ 3
    have hcols := domino_cells_col_ge_one T d' (by assumption)
    simp only [Domino.cells, Domino.shiftNat_cell1, Domino.shiftNat_cell2] at hd_cells
    have h : (d'.cell1.1 + 2, d'.cell1.2) ∈ ({(1, 2), (2, 2)} : Finset Cell) := by
      rw [← hd_cells]; exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- In `prependVertical T`, the only domino with cells `{(1,1), (1,2)}` is `vertical_1_1`. -/
lemma vertical_1_1_unique_in_prependVertical (T : DominoTiling n 2) (d : Domino)
    (hd : d ∈ (prependVertical T).dominos)
    (hd_cells : d.cells = ({(1, 1), (1, 2)} : Finset Cell)) :
    d = vertical_1_1 := by
  simp only [prependVertical, Finset.mem_insert, Finset.mem_image] at hd
  rcases hd with rfl | ⟨d', _, rfl⟩
  · rfl
  · -- d = d'.shiftNat 1, but shifted dominos have column ≥ 2
    have hcols := domino_cells_col_ge_one T d' (by assumption)
    simp only [Domino.cells, Domino.shiftNat_cell1, Domino.shiftNat_cell2] at hd_cells
    have h : (d'.cell1.1 + 1, d'.cell1.2) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
      rw [← hd_cells]; exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- Forward map for the Fibonacci recurrence bijection.
    Maps a 2×(n+2) tiling to either:
    - `inl T'` where T' is a 2×n tiling (horizontal case)
    - `inr T'` where T' is a 2×(n+1) tiling (vertical case) -/

lemma tiling_2_to_sum_from_sum (x : (DominoTiling n 2) ⊕ (DominoTiling (n + 1) 2)) :
    tiling_2_to_sum (tiling_2_from_sum x) = x := by
  rcases x with T | T
  · -- Horizontal case: x = inl T
    simp only [tiling_2_from_sum, Sum.elim_inl]
    -- prependHorizontalPair produces a tiling without vertical first column
    have hv : ¬hasVerticalFirstColumn (prependHorizontalPair T) := by
      intro ⟨d, hd_mem, hd_cells⟩
      simp only [prependHorizontalPair, Finset.mem_insert, Finset.mem_image] at hd_mem
      rcases hd_mem with rfl | rfl | ⟨d', _, rfl⟩
      · -- d = horizontal_1_1: cells = {(1,1), (2,1)} ≠ {(1,1), (1,2)}
        simp only [Domino.cells, horizontal_1_1] at hd_cells
        have h1 : ((1, 1) : Cell) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
          rw [← hd_cells]; exact Finset.mem_insert_self _ _
        have h2 : ((2, 1) : Cell) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
          rw [← hd_cells]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h2
        rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      · -- d = horizontal_1_2: cells = {(1,2), (2,2)} ≠ {(1,1), (1,2)}
        simp only [Domino.cells, horizontal_1_2] at hd_cells
        have h2 : ((2, 2) : Cell) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
          rw [← hd_cells]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h2
        rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
      · -- d = d'.shiftNat 2: cells have column ≥ 3
        have hcols := domino_cells_col_ge_one T d' (by assumption)
        simp only [Domino.cells, Domino.shiftNat_cell1, Domino.shiftNat_cell2] at hd_cells
        have h1 : (d'.cell1.1 + 2, d'.cell1.2) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
          rw [← hd_cells]; exact Finset.mem_insert_self _ _
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1
        rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    simp only [tiling_2_to_sum, dite_eq_right hv]
    -- The chosen dominos must be horizontal_1_1 and horizontal_1_2 by uniqueness
    have hpair := horizontalPair_of_not_hasVerticalFirstColumn (prependHorizontalPair T) hv
    have hd1_spec := Classical.choose_spec hpair.1
    have hd2_spec := Classical.choose_spec hpair.2
    have hd1_eq : Classical.choose hpair.1 = horizontal_1_1 :=
      horizontal_1_1_unique_in_prependHorizontalPair T _ hd1_spec.1 hd1_spec.2
    have hd2_eq : Classical.choose hpair.2 = horizontal_1_2 :=
      horizontal_1_2_unique_in_prependHorizontalPair T _ hd2_spec.1 hd2_spec.2
    -- Now use the existing roundtrip lemma
    simp only [hd1_eq, hd2_eq]
    have hmem1 : horizontal_1_1 ∈ (prependHorizontalPair T).dominos := by
      simp [prependHorizontalPair]
    have hmem2 : horizontal_1_2 ∈ (prependHorizontalPair T).dominos := by
      simp [prependHorizontalPair]
    -- The Gen version with canonical dominos equals the non-Gen version
    congr 1
    conv_lhs => rw [show restrictAfterHorizontalPairGen (prependHorizontalPair T) horizontal_1_1
      horizontal_1_2 hmem1 hmem2 rfl rfl = restrictAfterHorizontalPair (prependHorizontalPair T)
      hmem1 hmem2 from rfl]
    exact restrictAfterHorizontalPair_prependHorizontalPair T
  · -- Vertical case: x = inr T
    simp only [tiling_2_from_sum, Sum.elim_inr]
    -- prependVertical produces a tiling with vertical first column
    have hv : hasVerticalFirstColumn (prependVertical T) := by
      use vertical_1_1
      constructor
      · simp [prependVertical, vertical_1_1]
      · rfl
    simp only [tiling_2_to_sum, dite_eq_left hv]
    -- The chosen domino must be vertical_1_1 by uniqueness
    have hv_spec := Classical.choose_spec hv
    have hv_eq : Classical.choose hv = vertical_1_1 :=
      vertical_1_1_unique_in_prependVertical T _ hv_spec.1 hv_spec.2
    simp only [hv_eq]
    have hmem : vertical_1_1 ∈ (prependVertical T).dominos := by
      simp [prependVertical]
    -- The Gen version with canonical domino equals the non-Gen version
    congr 1
    conv_lhs => rw [show restrictAfterVerticalGen (prependVertical T) vertical_1_1
      hmem rfl = restrictAfterVertical (prependVertical T) hmem from
      restrictAfterVerticalGen_eq_restrictAfterVertical (prependVertical T) hmem]
    exact restrictAfterVertical_prependVertical T

/-- The forward map `tiling_2_to_sum` is surjective. -/
lemma tiling_2_to_sum_surjective :
    Function.Surjective (@tiling_2_to_sum n) := fun x =>
  ⟨tiling_2_from_sum x, tiling_2_to_sum_from_sum x⟩

/-- The backward map `tiling_2_from_sum` is injective. -/
lemma tiling_2_from_sum_injective :
    Function.Injective (@tiling_2_from_sum n) := fun x y h => by
  have hx := tiling_2_to_sum_from_sum x
  have hy := tiling_2_to_sum_from_sum y
  rw [h] at hx
  exact hx.symm.trans hy

/-- For finsets with attach.image and double function application, the image under h is preserved
    when h (g (f x)) = h x. -/

lemma image_preserved_under_double_roundtrip' {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : (x : α) → x ∈ S → β) (g : β → α) (h : α → γ)
    (hfgh : ∀ x (hx : x ∈ S), h (g (f x hx)) = h x) :
    ((S.attach.image (fun ⟨x, hx⟩ => f x hx)).image g).image h = S.image h := by
  ext c
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨b, ⟨a, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨x, hx, (hfgh x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g (f x hx), ⟨f x hx, ⟨x, hx, rfl⟩, rfl⟩, hfgh x hx⟩

/-- insert (h v) ((S.erase v).image h) = S.image h when v ∈ S -/
lemma insert_erase_image_eq' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (v : α) (h : α → β) (hv : v ∈ S) :
    insert (h v) ((S.erase v).image h) = S.image h := by
  ext b
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨a, ⟨hne, ha⟩, rfl⟩)
    · exact ⟨v, hv, rfl⟩
    · exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    by_cases heq : a = v
    · left; rw [heq]
    · right; exact ⟨a, ⟨heq, ha⟩, rfl⟩

/-- insert (h v1) (insert (h v2) (((S.erase v1).erase v2).image h)) = S.image h when v1, v2 ∈ S -/
lemma insert_insert_erase_erase_image_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (v1 v2 : α) (h : α → β) (hv1 : v1 ∈ S) (hv2 : v2 ∈ S) :
    insert (h v1) (insert (h v2) (((S.erase v1).erase v2).image h)) = S.image h := by
  ext b
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro (rfl | rfl | ⟨a, ⟨hne2, hne1, ha⟩, rfl⟩)
    · exact ⟨v1, hv1, rfl⟩
    · exact ⟨v2, hv2, rfl⟩
    · exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    by_cases heq1 : a = v1
    · left; rw [heq1]
    · by_cases heq2 : a = v2
      · right; left; rw [heq2]
      · right; right; exact ⟨a, ⟨heq2, heq1, ha⟩, rfl⟩

/-- The roundtrip `tiling_2_from_sum (tiling_2_to_sum T)` produces a tiling that is
    `TilingEquiv` to `T` (same cell coverage).

    This establishes that the bijection preserves cell coverage, even though structural
    equality may fail due to the `Domino` representation issue (cell1/cell2 ordering).

    Combined with `right_inv`, this proves that `tiling_2_to_sum` and `tiling_2_from_sum`
    form a bijection at the level of cell coverage, establishing the Fibonacci recurrence
    for counting 2×n domino tilings.

    **Proof status**: FULLY PROVED
    - Vertical case: PROVED (uses helper lemmas `image_preserved_under_double_roundtrip'`
      and `insert_erase_image_eq'`)
    - Horizontal case: PROVED (uses helper lemma `insert_insert_erase_erase_image_eq`) -/

lemma tiling_2_roundtrip_TilingEquiv (T : DominoTiling (n + 2) 2) :
    TilingEquiv (tiling_2_from_sum (tiling_2_to_sum T)) T := by
  unfold TilingEquiv tiling_2_to_sum tiling_2_from_sum
  split_ifs with hv
  · -- Vertical case: hasVerticalFirstColumn T
    simp only [Sum.elim_inr]
    -- We need: (prependVertical (restrictAfterVerticalGen T v ...)).dominos.image cells = T.dominos.image cells
    let v := Classical.choose hv
    let hv_spec := Classical.choose_spec hv
    let hv_mem := hv_spec.1
    let hv_cells := hv_spec.2
    -- The roundtrip dominos are:
    -- insert vertical_1_1 ((restrictAfterVerticalGen T v hv_mem hv_cells).dominos.image (shiftNat 1))
    -- = insert vertical_1_1 (((T.dominos.erase v).attach.image (shiftNeg 1)).image (shiftNat 1))
    simp only [prependVertical, restrictAfterVerticalGen]
    -- Now we need to show:
    -- (insert vertical_1_1 (((T.dominos.erase v).attach.image ...).image (shiftNat 1))).image cells
    -- = T.dominos.image cells
    rw [Finset.image_insert]
    -- LHS = insert (vertical_1_1.cells) (((...).image (shiftNat 1)).image cells)
    -- We need to show this equals T.dominos.image cells
    -- Step 1: Show (((...).image (shiftNat 1)).image cells = (T.dominos.erase v).image cells
    have hshift : ∀ d (hd : d ∈ T.dominos.erase v),
        ((d.shiftNeg 1 (domino_col_ge_two_of_disjoint_from_first_col T v hv_mem hv_cells d
          (Finset.mem_of_mem_erase hd) (Finset.mem_erase.mp hd).1).1
          (domino_col_ge_two_of_disjoint_from_first_col T v hv_mem hv_cells d
          (Finset.mem_of_mem_erase hd) (Finset.mem_erase.mp hd).1).2).shiftNat 1).cells = d.cells := by
      intro d hd
      exact Domino.shiftNat_shiftNeg_cells d 1 _ _
    have heq_erase := image_preserved_under_double_roundtrip' (T.dominos.erase v)
      (fun d hd => d.shiftNeg 1
        (domino_col_ge_two_of_disjoint_from_first_col T v hv_mem hv_cells d
          (Finset.mem_of_mem_erase hd) (Finset.mem_erase.mp hd).1).1
        (domino_col_ge_two_of_disjoint_from_first_col T v hv_mem hv_cells d
          (Finset.mem_of_mem_erase hd) (Finset.mem_erase.mp hd).1).2)
      (fun d => d.shiftNat 1) Domino.cells hshift
    rw [heq_erase]
    -- Now: insert (vertical_1_1.cells) ((T.dominos.erase v).image cells) = T.dominos.image cells
    -- Since vertical_1_1.cells = v.cells, this follows from insert_erase_image_eq'
    have hv_cells_eq : vertical_1_1.cells = v.cells := by rw [vertical_1_1_cells, hv_cells]
    rw [hv_cells_eq]
    exact insert_erase_image_eq' T.dominos v Domino.cells hv_mem
  · -- Horizontal case: ¬hasVerticalFirstColumn T
    simp only [Sum.elim_inl]
    -- Get the horizontal pair dominos from the hypothesis
    let hpair := horizontalPair_of_not_hasVerticalFirstColumn T hv
    let d1 := Classical.choose hpair.1
    let hd1_spec := Classical.choose_spec hpair.1
    let hd1_mem := hd1_spec.1
    let hd1_cells := hd1_spec.2
    let d2 := Classical.choose hpair.2
    let hd2_spec := Classical.choose_spec hpair.2
    let hd2_mem := hd2_spec.1
    let hd2_cells := hd2_spec.2
    -- The roundtrip dominos are:
    -- insert horizontal_1_1 (insert horizontal_1_2 ((restrictAfterHorizontalPairGen T d1 d2 ...).dominos.image (shiftNat 2)))
    simp only [prependHorizontalPair, restrictAfterHorizontalPairGen]
    -- Now we need to show:
    -- (insert horizontal_1_1 (insert horizontal_1_2 (((T.dominos.erase d1).erase d2).attach.image ...).image (shiftNat 2))).image cells
    -- = T.dominos.image cells
    rw [Finset.image_insert, Finset.image_insert]
    -- LHS = insert (horizontal_1_1.cells) (insert (horizontal_1_2.cells) (((...).image (shiftNat 2)).image cells))
    -- Step 1: Show (((...).image (shiftNat 2)).image cells = ((T.dominos.erase d1).erase d2).image cells
    have hshift : ∀ d (hd : d ∈ (T.dominos.erase d1).erase d2),
        let hd' := Finset.mem_erase.mp hd
        let hd'' := Finset.mem_erase.mp (Finset.mem_of_mem_erase hd)
        let hcols := other_dominos_col_ge_3_gen T d1 d2 hd1_mem hd2_mem hd1_cells hd2_cells d
                       (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hd''.1 hd'.1
        ((d.shiftNeg 2 hcols.1 hcols.2).shiftNat 2).cells = d.cells := by
      intro d hd
      exact Domino.shiftNat_shiftNeg_cells d 2 _ _
    have heq_erase := image_preserved_under_double_roundtrip' ((T.dominos.erase d1).erase d2)
      (fun d hd =>
        let hd' := Finset.mem_erase.mp hd
        let hd'' := Finset.mem_erase.mp (Finset.mem_of_mem_erase hd)
        let hcols := other_dominos_col_ge_3_gen T d1 d2 hd1_mem hd2_mem hd1_cells hd2_cells d
                       (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hd''.1 hd'.1
        d.shiftNeg 2 hcols.1 hcols.2)
      (fun d => d.shiftNat 2) Domino.cells hshift
    rw [heq_erase]
    -- Now: insert (horizontal_1_1.cells) (insert (horizontal_1_2.cells) (((T.dominos.erase d1).erase d2).image cells))
    --    = T.dominos.image cells
    -- Since horizontal_1_1.cells = d1.cells and horizontal_1_2.cells = d2.cells,
    -- this follows from insert_insert_erase_erase_image_eq
    have hd1_cells_eq : horizontal_1_1.cells = d1.cells := by rw [horizontal_1_1_cells, hd1_cells]
    have hd2_cells_eq : horizontal_1_2.cells = d2.cells := by rw [horizontal_1_2_cells, hd2_cells]
    rw [hd1_cells_eq, hd2_cells_eq]
    exact insert_insert_erase_erase_image_eq T.dominos d1 d2 Domino.cells hd1_mem hd2_mem

/-- The backward map `tiling_2_from_sum` is surjective up to `TilingEquiv`.
    For any tiling `T : DominoTiling (n+2) 2`, there exists `x` such that
    `tiling_2_from_sum x` is `TilingEquiv` to `T`.

    This follows from `tiling_2_roundtrip_TilingEquiv`: taking `x = tiling_2_to_sum T`,
    we have `TilingEquiv (tiling_2_from_sum x) T`.

    Combined with `tiling_2_from_sum_injective`, this establishes that `tiling_2_from_sum`
    is a bijection between `DominoTiling n 2 ⊕ DominoTiling (n+1) 2` and the `TilingEquiv`
    equivalence classes of `DominoTiling (n+2) 2`. This proves the Fibonacci recurrence
    for counting 2×n domino tilings at the level of cell coverage.

    **Note**: Structural equality (`=`) fails for the `left_inv` direction because tilings
    may use "flipped" dominos (e.g., `vertical_1_1_flip` instead of `vertical_1_1`).
    However, the mathematical content is correct: the roundtrip preserves cell coverage
    (`TilingEquiv`), and the bijection at the cell level is established. -/

lemma tiling_2_from_sum_surjective_up_to_TilingEquiv (T : DominoTiling (n + 2) 2) :
    ∃ x, TilingEquiv (tiling_2_from_sum x) T :=
  ⟨tiling_2_to_sum T, tiling_2_roundtrip_TilingEquiv T⟩

end DominoTiling

@[simp]
lemma mkHorizontalDomino_cell1 (x y : ℕ) : (mkHorizontalDomino x y).cell1 = (x, y) := rfl

@[simp]
lemma mkHorizontalDomino_cell2 (x y : ℕ) : (mkHorizontalDomino x y).cell2 = (x + 1, y) := rfl

@[simp]
lemma mkVerticalDomino_cell1 (x y : ℕ) : (mkVerticalDomino x y).cell1 = (x, y) := rfl

@[simp]
lemma mkVerticalDomino_cell2 (x y : ℕ) : (mkVerticalDomino x y).cell2 = (x, y + 1) := rfl

@[simp]
lemma isHorizontal_mkHorizontalDomino (x y : ℕ) : (mkHorizontalDomino x y).isHorizontal := rfl

@[simp]
lemma isVertical_mkVerticalDomino (x y : ℕ) : (mkVerticalDomino x y).isVertical := rfl

/-- reflectCell3 is an involution on cells with row in {1, 2, 3}. -/
lemma reflectCell3_involutive (c : Cell) (h1 : c.2 ≥ 1) (h2 : c.2 ≤ 3) :
    reflectCell3 (reflectCell3 c) = c := by
  simp only [reflectCell3]
  ext <;> omega

/-- For a domino in Rectangle n 3, cell1 has row ≥ 1. -/
lemma domino_cell1_row_ge' {n : ℕ} {d : Domino} (hd : d.cells ⊆ Rectangle n 3) :
    d.cell1.2 ≥ 1 := by
  have h : d.cell1 ∈ d.cells := by simp [Domino.cells]
  have h' := hd h
  rw [mem_Rectangle] at h'
  exact h'.2.2.1

/-- For a domino in Rectangle n 3, cell2 has row ≥ 1. -/
lemma domino_cell2_row_ge' {n : ℕ} {d : Domino} (hd : d.cells ⊆ Rectangle n 3) :
    d.cell2.2 ≥ 1 := by
  have h : d.cell2 ∈ d.cells := by simp [Domino.cells]
  have h' := hd h
  rw [mem_Rectangle] at h'
  exact h'.2.2.1

/-- reflectDomino3 preserves minCol. -/
lemma reflectDomino3_minCol {d : Domino} (h1 : d.cell1.2 ≤ 3) (h2 : d.cell2.2 ≤ 3) :
    (reflectDomino3 d h1 h2).minCol = d.minCol := by
  simp only [Domino.minCol, reflectDomino3, reflectCell3]

/-- reflectDomino3 preserves maxCol. -/
lemma reflectDomino3_maxCol {d : Domino} (h1 : d.cell1.2 ≤ 3) (h2 : d.cell2.2 ≤ 3) :
    (reflectDomino3 d h1 h2).maxCol = d.maxCol := by
  simp only [Domino.maxCol, reflectDomino3, reflectCell3]

/-- Key property: For each domino in T, there's a corresponding reflected domino in reflectTiling3 T
    with the same minCol and maxCol. This captures the essential fact that horizontal reflection
    only changes row coordinates, not column coordinates. -/

lemma reflectTiling3_dominos_minCol_maxCol {n : ℕ} (T : DominoTiling n 3) :
    ∀ d ∈ T.dominos, ∃ d' ∈ (reflectTiling3 T).dominos, d'.minCol = d.minCol ∧ d'.maxCol = d.maxCol := by
  intro d hd
  -- The reflected domino d' is reflectDomino3 d
  let h1 := domino_cell1_row_le' (T.dominos_in_rect d hd)
  let h2 := domino_cell2_row_le' (T.dominos_in_rect d hd)
  use reflectDomino3 d h1 h2
  constructor
  · -- Show d' is in (reflectTiling3 T).dominos
    simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe]
    exact ⟨d, hd, rfl⟩
  · -- Show minCol and maxCol are preserved
    exact ⟨reflectDomino3_minCol h1 h2, reflectDomino3_maxCol h1 h2⟩

/-- Reflection preserves faultfreeness.

    The proof uses the key observation that horizontal reflection only changes row coordinates,
    not column coordinates. Therefore, minCol and maxCol of each domino are preserved.
    Since faults are determined solely by whether dominos span column boundaries
    (i.e., whether minCol ≤ k < maxCol for some k), reflection preserves faultfreeness. -/

lemma reflectTiling3_isFaultfree {n : ℕ} (T : DominoTiling n 3) (hfree : T.isFaultfree) :
    (reflectTiling3 T).isFaultfree := by
  intro k hk_ge1 hk_lt_n hfault
  -- Then T also has a fault at k
  have hfault_T : T.hasFaultAt k := by
    constructor
    · exact hfault.1
    constructor
    · exact hfault.2.1
    · intro d hd
      -- Get the corresponding reflected domino
      obtain ⟨d', hd'_mem, hd'_min, hd'_max⟩ := reflectTiling3_dominos_minCol_maxCol T d hd
      -- d' doesn't span column k (since there's a fault)
      have hd'_no_span := hfault.2.2 d' hd'_mem
      -- But d has the same minCol and maxCol as d'
      rw [← hd'_min, ← hd'_max]
      exact hd'_no_span
  -- But T is faultfree, contradiction
  exact hfree k hk_ge1 hk_lt_n hfault_T

/-- Reflection swaps top and bottom vertical dominos. -/
lemma reflectTiling3_hasTopVertical_iff_hasBottomVertical {n : ℕ} (T : DominoTiling n 3) (c : ℕ) :
    (reflectTiling3 T).hasTopVerticalInCol c ↔ T.hasBottomVerticalInCol c := by
  constructor
  · -- (→) If reflectTiling3 T has top vertical in column c, then T has bottom vertical in column c
    intro ⟨d, hd_mem, hd_vert, hd_col, hd_rows⟩
    -- d is in (reflectTiling3 T).dominos, so d = reflectDomino3 d' for some d' ∈ T.dominos
    simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe] at hd_mem
    obtain ⟨d', hd'_mem, rfl⟩ := hd_mem
    -- Show d' is vertical and in the bottom rows
    use d', hd'_mem
    constructor
    · -- d' is vertical: d'.cell1.1 = d'.cell2.1
      simp only [reflectDomino3, reflectCell3, Domino.isVertical] at hd_vert
      exact hd_vert
    constructor
    · -- d'.cell1.1 = c
      simp only [reflectDomino3, reflectCell3] at hd_col
      exact hd_col
    · -- d' is in bottom rows: reflectCell3 maps row y to 4-y, so 1↔3, 2↔2
      simp only [reflectDomino3, reflectCell3] at hd_rows
      rcases hd_rows with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> omega
      · left; constructor <;> omega
  · -- (←) If T has bottom vertical in column c, then reflectTiling3 T has top vertical in column c
    intro ⟨d, hd_mem, hd_vert, hd_col, hd_rows⟩
    -- The reflected domino is in reflectTiling3 T
    let d' := reflectDomino3 d (domino_cell1_row_le' (T.dominos_in_rect d hd_mem))
                               (domino_cell2_row_le' (T.dominos_in_rect d hd_mem))
    use d'
    constructor
    · -- d' ∈ (reflectTiling3 T).dominos
      simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe]
      exact ⟨d, hd_mem, rfl⟩
    constructor
    · -- d' is vertical
      simp only [d', reflectDomino3, reflectCell3, Domino.isVertical]
      exact hd_vert
    constructor
    · -- d'.cell1.1 = c
      simp only [d', reflectDomino3, reflectCell3]
      exact hd_col
    · -- d' is in top rows (rows 2,3): bottom rows (1,2) or (2,1) map to (3,2) or (2,3)
      simp only [d', reflectDomino3, reflectCell3]
      rcases hd_rows with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; constructor <;> omega
      · left; constructor <;> omega

/-- Reflection is an involution. -/
lemma reflectTiling3_involutive {n : ℕ} (T : DominoTiling n 3) :
    reflectTiling3 (reflectTiling3 T) = T := by
  -- Two DominoTilings are equal iff their dominos are equal (proof irrelevance for the rest)
  have h_dominos : (reflectTiling3 (reflectTiling3 T)).dominos = T.dominos := by
    ext d
    constructor
    · -- d ∈ (reflectTiling3 (reflectTiling3 T)).dominos → d ∈ T.dominos
      intro hd
      rw [reflectTiling3] at hd
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨d', hd', heq⟩ := hd
      rw [reflectTiling3] at hd'
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe] at hd'
      obtain ⟨d'', hd'', heq'⟩ := hd'
      subst heq heq'
      have hd''_rect := T.dominos_in_rect d'' hd''
      have hge1 := domino_cell1_row_ge' hd''_rect
      have hge2 := domino_cell2_row_ge' hd''_rect
      have hle1 := domino_cell1_row_le' hd''_rect
      have hle2 := domino_cell2_row_le' hd''_rect
      have h1' : (reflectDomino3 d'' hle1 hle2).cell1.2 ≤ 3 := by
        simp only [reflectDomino3, reflectCell3]; omega
      have h2' : (reflectDomino3 d'' hle1 hle2).cell2.2 ≤ 3 := by
        simp only [reflectDomino3, reflectCell3]; omega
      have hinv : reflectDomino3 (reflectDomino3 d'' hle1 hle2) h1' h2' = d'' := by
        ext <;> simp only [reflectDomino3, reflectCell3] <;> omega
      rw [hinv]
      exact hd''
    · -- d ∈ T.dominos → d ∈ (reflectTiling3 (reflectTiling3 T)).dominos
      intro hd
      have hd_rect := T.dominos_in_rect d hd
      have hge1 := domino_cell1_row_ge' hd_rect
      have hge2 := domino_cell2_row_ge' hd_rect
      have hle1 := domino_cell1_row_le' hd_rect
      have hle2 := domino_cell2_row_le' hd_rect
      rw [reflectTiling3]
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe]
      refine ⟨reflectDomino3 d hle1 hle2, ?_, ?_⟩
      · rw [reflectTiling3]
        simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
          ← Function.Embedding.toFun_eq_coe]
        exact ⟨d, hd, rfl⟩
      · ext <;> simp only [reflectDomino3, reflectCell3] <;> omega
  -- Now use h_dominos to conclude equality
  cases T with
  | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    have h : (reflectTiling3 (reflectTiling3 { dominos, dominos_in_rect, covers_all, pairwise_disjoint })).dominos = dominos := h_dominos
    cases hT : reflectTiling3 (reflectTiling3 { dominos, dominos_in_rect, covers_all, pairwise_disjoint }) with
    | mk dominos' dominos_in_rect' covers_all' pairwise_disjoint' =>
      rw [hT] at h
      simp only at h
      subst h
      rfl

/-- reflectTiling3 preserves TilingEquiv: if T₁ ≃ T₂ (same cell images),
    then reflectTiling3 T₁ ≃ reflectTiling3 T₂. -/

lemma reflectTiling3_preserves_TilingEquiv {n : ℕ} (T₁ T₂ : DominoTiling n 3)
    (h : DominoTiling.TilingEquiv T₁ T₂) :
    DominoTiling.TilingEquiv (reflectTiling3 T₁) (reflectTiling3 T₂) := by
  unfold DominoTiling.TilingEquiv at h ⊢
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
  · rintro ⟨d, ⟨d₁, hd₁, rfl⟩, rfl⟩
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
  · rintro ⟨d, ⟨d₂, hd₂, rfl⟩, rfl⟩
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

/-- TilingB is the reflection of TilingA. -/
lemma TilingB_eq_reflectTiling3_TilingA (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
    TilingB n hn hn_ge = reflectTiling3 (TilingA n hn hn_ge) := by
  -- Two DominoTiling structures are equal if their dominos fields are equal
  -- (the other fields are propositions, so equal by proof irrelevance)
  -- First show the dominos are equal, then use that to conclude
  have h_dominos : (TilingB n hn hn_ge).dominos = (reflectTiling3 (TilingA n hn hn_ge)).dominos := by
    -- Unfold the definitions
    simp only [TilingB, reflectTiling3, TilingA]
    -- Show the two Finsets are equal
    ext d
    constructor
    · -- d ∈ TilingB.dominos → d ∈ (reflectTiling3 TilingA).dominos
      intro hd
      simp only [Finset.mem_union, Finset.mem_singleton] at hd
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe]
      -- Case analysis on which subset d comes from
      rcases hd with ((((hbase | hleft) | hright) | hmid) | hbot)
      · -- d ∈ basementDominosB n (reflected from basementDominos)
        simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hbase
        obtain ⟨i, hi, rfl⟩ := hbase
        -- The original domino in basementDominos
        let d' : Domino := ⟨(2 * i + 1, 1), (2 * i + 2, 1),
              by simp only [ne_eq, Prod.mk.injEq, and_true]; omega,
              by right; exact ⟨rfl, Or.inl rfl⟩⟩
        refine ⟨d', ?_, ?_⟩
        · -- This domino is in TilingA.dominos
          simp only [Finset.mem_union, Finset.mem_singleton, basementDominos, Finset.mem_map,
            Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          left; left; left; left
          exact ⟨i, hi, rfl⟩
        · -- reflectDomino3 gives the right result
          simp only [reflectDomino3, reflectCell3, d']
      · -- d = leftWallB (reflected from leftWall)
        refine ⟨leftWall, ?_, ?_⟩
        · simp only [Finset.mem_union, Finset.mem_singleton]
          left; left; left; right; trivial
        · subst hleft
          simp only [reflectDomino3, reflectCell3, leftWall, leftWallB]
      · -- d = rightWallB n (reflected from rightWall n)
        refine ⟨rightWall n, ?_, ?_⟩
        · simp only [Finset.mem_union, Finset.mem_singleton]
          left; left; right; trivial
        · subst hright
          simp only [reflectDomino3, reflectCell3, rightWall, rightWallB]
      · -- d ∈ middleDominos n (unchanged by reflection since row 2 is fixed)
        simp only [middleDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hmid
        obtain ⟨i, hi, rfl⟩ := hmid
        let d' : Domino := ⟨(2 * i + 2, 2), (2 * i + 3, 2),
              by simp only [ne_eq, Prod.mk.injEq, and_true]; omega,
              by right; exact ⟨rfl, Or.inl rfl⟩⟩
        refine ⟨d', ?_, ?_⟩
        · simp only [Finset.mem_union, Finset.mem_singleton, middleDominos, Finset.mem_map,
            Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          left; right
          exact ⟨i, hi, rfl⟩
        · simp only [reflectDomino3, reflectCell3, d']
      · -- d ∈ bottomDominosB n (reflected from topDominos)
        simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hbot
        obtain ⟨i, hi, rfl⟩ := hbot
        let d' : Domino := ⟨(2 * i + 2, 3), (2 * i + 3, 3),
              by simp only [ne_eq, Prod.mk.injEq, and_true]; omega,
              by right; exact ⟨rfl, Or.inl rfl⟩⟩
        refine ⟨d', ?_, ?_⟩
        · simp only [Finset.mem_union, Finset.mem_singleton, topDominos, Finset.mem_map,
            Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          right
          exact ⟨i, hi, rfl⟩
        · simp only [reflectDomino3, reflectCell3, d']
    · -- d ∈ (reflectTiling3 TilingA).dominos → d ∈ TilingB.dominos
      intro hd
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨d', hd'_mem, hd'_eq⟩ := hd
      simp only [Finset.mem_union, Finset.mem_singleton] at hd'_mem ⊢
      -- Case analysis on which subset d' comes from
      rcases hd'_mem with ((((hbase | hleft) | hright) | hmid) | htop)
      · -- d' ∈ basementDominos n → d ∈ basementDominosB n
        simp only [basementDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hbase
        obtain ⟨i, hi, rfl⟩ := hbase
        left; left; left; left
        simp only [basementDominosB, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
        use i, hi
        simp only [reflectDomino3, reflectCell3] at hd'_eq
        exact hd'_eq
      · -- d' = leftWall → d = leftWallB
        left; left; left; right
        subst hleft
        simp only [reflectDomino3, reflectCell3, leftWall, leftWallB] at hd'_eq ⊢
        exact hd'_eq.symm
      · -- d' = rightWall n → d = rightWallB n
        left; left; right
        subst hright
        simp only [reflectDomino3, reflectCell3, rightWall, rightWallB] at hd'_eq ⊢
        exact hd'_eq.symm
      · -- d' ∈ middleDominos n → d ∈ middleDominos n
        simp only [middleDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hmid
        obtain ⟨i, hi, rfl⟩ := hmid
        left; right
        simp only [middleDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
        use i, hi
        simp only [reflectDomino3, reflectCell3] at hd'_eq
        exact hd'_eq
      · -- d' ∈ topDominos n → d ∈ bottomDominosB n
        simp only [topDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at htop
        obtain ⟨i, hi, rfl⟩ := htop
        right
        simp only [bottomDominosB, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
        use i, hi
        simp only [reflectDomino3, reflectCell3] at hd'_eq
        exact hd'_eq
  -- Now conclude equality of the DominoTiling structures
  cases hB : TilingB n hn hn_ge
  cases hR : reflectTiling3 (TilingA n hn hn_ge)
  simp only [DominoTiling.mk.injEq]
  simp only [hB, hR] at h_dominos
  exact h_dominos

/-- Helper lemma: a domino from middleDominos. -/
lemma middleDominos_mem (n i : ℕ) (hi : i < n / 2 - 1) :
    ∃ d ∈ middleDominos n, d.cell1 = (2 * i + 2, 2) ∧ d.cell2 = (2 * i + 3, 2) := by
  simp only [middleDominos, Finset.mem_map, Finset.mem_range]
  refine ⟨_, ⟨i, hi, rfl⟩, rfl, rfl⟩

/-- Helper lemma: a domino from basementDominos. -/
lemma basementDominos_mem (n i : ℕ) (hi : i < n / 2) :
    ∃ d ∈ basementDominos n, d.cell1 = (2 * i + 1, 1) ∧ d.cell2 = (2 * i + 2, 1) := by
  simp only [basementDominos, Finset.mem_map, Finset.mem_range]
  refine ⟨_, ⟨i, hi, rfl⟩, rfl, rfl⟩

/-- Helper lemma: a domino from topDominos. -/
lemma topDominos_mem (n i : ℕ) (hi : i < n / 2 - 1) :
    ∃ d ∈ topDominos n, d.cell1 = (2 * i + 2, 3) ∧ d.cell2 = (2 * i + 3, 3) := by
  simp only [topDominos, Finset.mem_map, Finset.mem_range]
  refine ⟨_, ⟨i, hi, rfl⟩, rfl, rfl⟩

/-- For col in [1,n], there exists i < n/2 such that col ∈ {2i+1, 2i+2}. -/
lemma col_in_basement_range (n col : ℕ) (hn : Even n) (hcol_ge : col ≥ 1) (hcol_le : col ≤ n) :
    ∃ i < n / 2, col = 2 * i + 1 ∨ col = 2 * i + 2 := by
  use (col - 1) / 2
  constructor
  · obtain ⟨k, hk⟩ := hn; subst hk
    have h2 : col - 1 < 2 * k := by omega
    have : (col - 1) / 2 < k := Nat.div_lt_of_lt_mul h2
    have hn2 : (2 * k) / 2 = k := Nat.mul_div_cancel_left k (by omega : 0 < 2)
    omega
  · have hmod : (col - 1) % 2 = 0 ∨ (col - 1) % 2 = 1 := by omega
    rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega

/-- For col in [2,n-1], there exists i < n/2-1 such that col ∈ {2i+2, 2i+3}. -/
lemma col_in_middle_range (n col : ℕ) (hn : Even n) (hn_ge : n ≥ 2)
    (hcol_ge : col ≥ 2) (hcol_le : col ≤ n - 1) :
    ∃ i < n / 2 - 1, col = 2 * i + 2 ∨ col = 2 * i + 3 := by
  use (col - 2) / 2
  constructor
  · obtain ⟨k, hk⟩ := hn; subst hk
    have h3 : col - 2 < 2 * (k - 1) := by omega
    have : (col - 2) / 2 < k - 1 := Nat.div_lt_of_lt_mul h3
    have hn2 : (2 * k) / 2 = k := Nat.mul_div_cancel_left k (by omega : 0 < 2)
    omega
  · have hmod : (col - 2) % 2 = 0 ∨ (col - 2) % 2 = 1 := by omega
    rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega

/-- Row 1 of the rectangle is covered by basement dominos in TilingA. -/
lemma TilingA_row1_covered (n col : ℕ) (hn : Even n) (hn_ge : n ≥ 2)
    (hcol_ge : col ≥ 1) (hcol_le : col ≤ n) :
    ∃ d ∈ (TilingA n hn hn_ge).dominos, (col, 1) ∈ d.cells := by
  have ⟨i, hi, hcol_eq⟩ := col_in_basement_range n col hn hcol_ge hcol_le
  obtain ⟨d, hd_mem, hd1, hd2⟩ := basementDominos_mem n i hi
  use d
  constructor
  · simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
    left; left; left; left; exact hd_mem
  · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton, hd1, hd2]
    rcases hcol_eq with rfl | rfl <;> simp

/-- Row 2 of the rectangle is covered by leftWall, rightWall, or middleDominos in TilingA. -/
lemma TilingA_row2_covered (n col : ℕ) (hn : Even n) (hn_ge : n ≥ 2)
    (hcol_ge : col ≥ 1) (hcol_le : col ≤ n) :
    ∃ d ∈ (TilingA n hn hn_ge).dominos, (col, 2) ∈ d.cells := by
  rcases Nat.eq_or_lt_of_le hcol_ge with rfl | hcol_gt1
  · -- col = 1: covered by leftWall
    use leftWall
    constructor
    · simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
      left; left; left; right; trivial
    · simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
      left; trivial
  · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
    · -- col = n: covered by rightWall
      use rightWall n
      constructor
      · simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
        left; left; right; trivial
      · simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        left; rw [heq]
    · -- 1 < col < n: covered by middleDominos
      have hcol_ge2 : col ≥ 2 := by omega
      have hcol_le_nm1 : col ≤ n - 1 := by omega
      have ⟨i, hi, hcol_eq⟩ := col_in_middle_range n col hn hn_ge hcol_ge2 hcol_le_nm1
      obtain ⟨d, hd_mem, hd1, hd2⟩ := middleDominos_mem n i hi
      use d
      constructor
      · simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
        left; right; exact hd_mem
      · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton, hd1, hd2]
        rcases hcol_eq with rfl | rfl <;> simp

/-- Row 3 of the rectangle is covered by leftWall, rightWall, or topDominos in TilingA. -/
lemma TilingA_row3_covered (n col : ℕ) (hn : Even n) (hn_ge : n ≥ 2)
    (hcol_ge : col ≥ 1) (hcol_le : col ≤ n) :
    ∃ d ∈ (TilingA n hn hn_ge).dominos, (col, 3) ∈ d.cells := by
  rcases Nat.eq_or_lt_of_le hcol_ge with rfl | hcol_gt1
  · -- col = 1: covered by leftWall
    use leftWall
    constructor
    · simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
      left; left; left; right; trivial
    · simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
      right; trivial
  · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
    · -- col = n: covered by rightWall
      use rightWall n
      constructor
      · simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
        left; left; right; trivial
      · simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        right; rw [heq]
    · -- 1 < col < n: covered by topDominos
      have hcol_ge2 : col ≥ 2 := by omega
      have hcol_le_nm1 : col ≤ n - 1 := by omega
      have ⟨i, hi, hcol_eq⟩ := col_in_middle_range n col hn hn_ge hcol_ge2 hcol_le_nm1
      obtain ⟨d, hd_mem, hd1, hd2⟩ := topDominos_mem n i hi
      use d
      constructor
      · simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
        right; exact hd_mem
      · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton, hd1, hd2]
        rcases hcol_eq with rfl | rfl <;> simp

/-- The tilings A_n are faultfree.

    The basement dominos prevent faults between columns 2i-1 and 2i,
    while the top dominos prevent faults between columns 2i and 2i+1. -/

lemma TilingA_isFaultfree (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
    (TilingA n hn hn_ge).isFaultfree := by
  intro k hk_ge1 hk_lt_n
  unfold DominoTiling.hasFaultAt
  push Not
  intro _ _
  -- We need to find a domino that spans column k
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · -- k is even, so k = 2j for some j ≥ 1
    obtain ⟨j, hj⟩ := hk_even
    have hj_pos : j ≥ 1 := by omega
    have hj_bound : j - 1 < n / 2 - 1 := by
      have hn2 : n / 2 * 2 = n := Nat.div_two_mul_two_of_even hn
      have : k < n := hk_lt_n
      have : j + j < n := by omega
      have : j < n / 2 := by omega
      omega
    -- The middle domino at index j-1 spans columns 2j to 2j+1
    obtain ⟨d, hd_mem, hd1, hd2⟩ := middleDominos_mem n (j - 1) hj_bound
    use d
    constructor
    · -- Show this domino is in the tiling
      simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
      left; right
      exact hd_mem
    · -- Show it spans column k
      simp only [Domino.minCol, Domino.maxCol, hd1, hd2]
      have h1 : 2 * (j - 1) + 2 = 2 * j := by omega
      have h2 : 2 * (j - 1) + 3 = 2 * j + 1 := by omega
      constructor
      · -- minCol ≤ k
        simp only [min_def]
        split_ifs <;> omega
      · -- k < maxCol
        simp only [max_def]
        split_ifs <;> omega
  · -- k is odd, so k = 2j + 1 for some j ≥ 0
    obtain ⟨j, hj⟩ := hk_odd
    have hj_bound : j < n / 2 := by
      have hn2 : n / 2 * 2 = n := Nat.div_two_mul_two_of_even hn
      have : k < n := hk_lt_n
      have : 2 * j + 1 < n := by omega
      omega
    -- The basement domino at index j spans columns (2j+1) to (2j+2)
    obtain ⟨d, hd_mem, hd1, hd2⟩ := basementDominos_mem n j hj_bound
    use d
    constructor
    · -- Show this domino is in the tiling
      simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
      left; left; left; left
      exact hd_mem
    · -- Show it spans column k
      simp only [Domino.minCol, Domino.maxCol, hd1, hd2]
      constructor
      · -- minCol ≤ k
        simp only [min_def]
        split_ifs <;> omega
      · -- k < maxCol
        simp only [max_def]
        split_ifs <;> omega

/-- The tilings B_n are faultfree (by reflection symmetry with A_n). -/
lemma TilingB_isFaultfree (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
    (TilingB n hn hn_ge).isFaultfree := by
  rw [TilingB_eq_reflectTiling3_TilingA]
  exact reflectTiling3_isFaultfree (TilingA n hn hn_ge) (TilingA_isFaultfree n hn hn_ge)

/-- The tiling C is faultfree. -/
lemma TilingC_isFaultfree : TilingC.isFaultfree := by
  intro k hk_ge1 hk_lt2
  -- k must be 1 (since 1 ≤ k < 2)
  interval_cases k
  -- k = 1: show there's no fault at column 1
  intro hfault
  obtain ⟨_, _, hdominos⟩ := hfault
  -- The first domino d1 spans columns 1 and 2, so it crosses the potential fault line
  -- d1.minCol = 1 and d1.maxCol = 2, so d1.minCol ≤ 1 ∧ 1 < d1.maxCol
  have hd1 : { cell1 := (1, 1), cell2 := (2, 1),
               distinct := (by decide : (1, 1) ≠ (2, 1)),
               adjacent := (by right; exact ⟨rfl, Or.inl rfl⟩) : Domino } ∈ TilingC.dominos := by
    simp only [TilingC, Finset.mem_insert, Finset.mem_singleton, true_or]
  have h := hdominos _ hd1
  -- h : ¬(d.minCol ≤ 1 ∧ 1 < d.maxCol)
  apply h
  constructor
  · -- d.minCol ≤ 1, i.e., min 1 2 ≤ 1
    simp only [Domino.minCol]
    decide
  · -- 1 < d.maxCol, i.e., 1 < max 1 2
    simp only [Domino.maxCol]
    decide

/-- Tiling A_n has a vertical domino in the top two squares of column 1. -/
lemma TilingA_hasTopVertical (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
    (TilingA n hn hn_ge).hasTopVerticalInCol 1 := by
  -- We show that leftWall is in the dominos and satisfies the property
  use leftWall
  constructor
  · -- leftWall ∈ dominos
    simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
    left; left; left; right
    trivial
  · -- leftWall.isVertical ∧ leftWall.cell1.1 = 1 ∧ ...
    constructor
    · -- isVertical: cell1.1 = cell2.1 = 1
      rfl
    constructor
    · -- cell1.1 = 1
      rfl
    · -- rows condition: cell1.2 = 3 - 1 = 2 and cell2.2 = 3
      left
      constructor <;> rfl

/-- Tiling B_n has a vertical domino in the bottom two squares of column 1. -/
lemma TilingB_hasBottomVertical (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) :
    (TilingB n hn hn_ge).hasBottomVerticalInCol 1 := by
  unfold DominoTiling.hasBottomVerticalInCol
  use leftWallB
  constructor
  · -- leftWallB ∈ (TilingB n hn hn_ge).dominos
    simp only [TilingB, Finset.mem_union, Finset.mem_singleton]
    left; left; left; right
    trivial
  · constructor
    · -- leftWallB.isVertical
      unfold Domino.isVertical
      simp [leftWallB]
    · constructor
      · -- leftWallB.cell1.1 = 1
        simp [leftWallB]
      · -- (leftWallB.cell1.2 = 1 ∧ leftWallB.cell2.2 = 2) ∨ (leftWallB.cell1.2 = 2 ∧ leftWallB.cell2.2 = 1)
        right
        simp [leftWallB]

/-- Tiling C has no vertical domino in column 1. -/
lemma TilingC_noVerticalInCol1 : ¬TilingC.hasVerticalInCol 1 := by
  simp only [DominoTiling.hasVerticalInCol, TilingC, Finset.mem_insert, Finset.mem_singleton,
    Domino.isVertical]
  intro ⟨d, hd_mem, hd_vert, hd_col⟩
  rcases hd_mem with rfl | rfl | rfl <;> simp_all

/-- A tiling with a vertical domino in the top of column c has n ≥ c.
    This follows because the domino must be within the rectangle. -/

lemma hasTopVerticalInCol_implies_n_ge (n : ℕ) (T : DominoTiling n 3) (c : ℕ)
    (htop : T.hasTopVerticalInCol c) : n ≥ c := by
  obtain ⟨d, hd_mem, hd_vert, hd_col, hd_rows⟩ := htop
  have h := T.dominos_in_rect d hd_mem
  have hcell1 : d.cell1 ∈ d.cells := by simp [Domino.cells]
  have hcell1_rect : d.cell1 ∈ Rectangle n 3 := h hcell1
  simp only [Rectangle, Finset.mem_map, Finset.mem_product, Finset.mem_range,
             ← Function.Embedding.toFun_eq_coe] at hcell1_rect
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := hcell1_rect
  have hcell1_fst : d.cell1.1 = x + 1 := by
    have : (x + 1, y + 1) = d.cell1 := hxy
    rw [← this]
  rw [hd_col] at hcell1_fst
  omega

/-- A rectangle R_{n,3} can only be tiled by dominos if n is even or n = 0.

    This follows from the parity argument: 3n squares must be covered by dominos
    (each covering 2 squares), so 3n must be even, hence n must be even. -/

lemma rectangle_tileable_iff_even (n : ℕ) :
    Nonempty (DominoTiling n 3) → Even n ∨ n = 0 := by
  intro ⟨T⟩
  -- Rectangle n 3 has 3n cells, each domino covers 2 cells
  -- Since dominos partition the rectangle, 3n must be even
  -- Since 3 is odd, n must be even
  have h_disjoint : (T.dominos : Set Domino).PairwiseDisjoint Domino.cells := by
    intro d₁ hd₁ d₂ hd₂ hne
    exact T.pairwise_disjoint d₁ hd₁ d₂ hd₂ hne
  have h_sum : (T.dominos.biUnion Domino.cells).card = T.dominos.sum (fun d => d.cells.card) :=
    card_biUnion h_disjoint
  have h_cells_card : ∀ d : Domino, d.cells.card = 2 := fun d =>
    card_pair d.distinct
  have h_sum_two : T.dominos.sum (fun d => d.cells.card) = 2 * T.dominos.card := by
    simp only [h_cells_card, sum_const, smul_eq_mul, mul_comm]
  have h_rect_card : (Rectangle n 3).card = n * 3 := by
    simp only [Rectangle, card_map, card_product, card_range]
  have h_even_3n : Even (n * 3) := by
    rw [T.covers_all, h_rect_card] at h_sum
    rw [h_sum_two] at h_sum
    rw [h_sum]
    exact even_two_mul _
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact Or.inr hn
  · left
    rw [Nat.even_mul] at h_even_3n
    exact h_even_3n.resolve_right (by decide)

/-- Helper lemma for the base case: If T has a top vertical domino in column 1,
    then the cell (1,1) must be covered by a horizontal domino going right.
    This gives us the basement domino {(1,1), (2,1)} for i=1. -/

lemma base_case_basement (n : ℕ) (T : DominoTiling n 3)
    (htop : T.hasTopVerticalInCol 1) (hn : n ≥ 2) :
    ∃ d ∈ T.dominos, d.cells = {(1, 1), (2, 1)} := by
  have h11_in : (1, 1) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
  obtain ⟨d, hd_mem, hd_cov⟩ := T.cell_covered (1, 1) h11_in
  obtain ⟨d_top, hd_top_mem, hd_top_vert, hd_top_col, hd_top_rows⟩ := htop
  have hd_in_rect := T.dominos_in_rect d hd_mem
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := hd_in_rect (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := hd_in_rect (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd_cov
  have hd_top_c2_col : d_top.cell2.1 = 1 := hd_top_vert.symm.trans hd_top_col
  have hd_top_covers_12 : (1, 2) ∈ d_top.cells := by
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
    rcases hd_top_rows with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
    · left; ext; exact hd_top_col.symm; omega
    · right; ext; exact hd_top_c2_col.symm; omega
  have hd_ne_top : d ≠ d_top := by
    intro heq; subst heq
    rcases hd_cov with hc | hc
    · rcases hd_top_rows with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
      · have : (1 : ℕ) = 2 := by rw [← hc] at hr1; exact hr1
        omega
      · have : (1 : ℕ) = 3 := by rw [← hc] at hr1; exact hr1
        omega
    · rcases hd_top_rows with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
      · have : (1 : ℕ) = 3 := by rw [← hc] at hr2; exact hr2
        omega
      · have : (1 : ℕ) = 2 := by rw [← hc] at hr2; exact hr2
        omega
  have hd_not_12 : (1, 2) ∉ d.cells := by
    intro h12
    have := DominoTiling.cell_covered_unique T (1, 2) d d_top hd_mem hd_top_mem h12 hd_top_covers_12
    exact hd_ne_top this
  use d, hd_mem
  rcases hd_cov with hc1 | hc2
  · have hc1_eq : d.cell1 = (1, 1) := hc1.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc2_col : d.cell2.1 = 1 := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · have hc2_eq : d.cell2 = (1, 2) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        exfalso; apply hd_not_12; simp [Domino.cells, hc2_eq]
      · have hc2_row : d.cell2.2 = 0 := by rw [hc1_eq] at h; omega
        have hge1 : d.cell2.2 ≥ 1 := hd_c2_in.2.2.1
        omega
    · have hc2_row : d.cell2.2 = 1 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · have hc2_eq : d.cell2 = (2, 1) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        simp only [Domino.cells, hc1_eq, hc2_eq]
      · have hc2_col : d.cell2.1 = 0 := by rw [hc1_eq] at h; omega
        have hge1 : d.cell2.1 ≥ 1 := hd_c2_in.1
        omega
  · have hc2_eq : d.cell2 = (1, 1) := hc2.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc1_col : d.cell1.1 = 1 := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · have hc1_row : d.cell1.2 = 0 := by rw [hc2_eq] at h; omega
        have hge1 : d.cell1.2 ≥ 1 := hd_c1_in.2.2.1
        omega
      · have hc1_eq : d.cell1 = (1, 2) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        exfalso; apply hd_not_12; simp [Domino.cells, hc1_eq]
    · have hc1_row : d.cell1.2 = 1 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · have hc1_col : d.cell1.1 = 0 := by rw [hc2_eq] at h; omega
        have hge1 : d.cell1.1 ≥ 1 := hd_c1_in.1
        omega
      · have hc1_eq' : d.cell1 = (2, 1) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        simp only [Domino.cells, hc1_eq', hc2_eq, Finset.pair_comm]

/-- If a domino d covers (2, 2), is contained in Rectangle n 3 (n ≥ 3), and
    doesn't cover (1, 2), then d.cells is one of:
    - {(2, 2), (3, 2)} (horizontal going right)
    - {(2, 1), (2, 2)} (vertical going down)
    - {(2, 2), (2, 3)} (vertical going up) -/

lemma domino_at_22_options (n : ℕ) (d : Domino)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (2, 2) ∈ d.cells)
    (h_not_12 : (1, 2) ∉ d.cells) :
    d.cells = {(2, 2), (3, 2)} ∨ d.cells = {(2, 1), (2, 2)} ∨ d.cells = {(2, 2), (2, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_12 ⊢
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · have hc1_eq : d.cell1 = (2, 2) := hc1.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc2_col : d.cell2.1 = 2 := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · have hc2_eq : d.cell2 = (2, 3) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (2, 1) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc2_row : d.cell2.2 = 2 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · have hc2_eq : d.cell2 = (3, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        left; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (1, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_12; right; exact hc2_eq.symm
  · have hc2_eq : d.cell2 = (2, 2) := hc2.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc1_col : d.cell1.1 = 2 := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · have hc1_eq : d.cell1 = (2, 1) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq]
      · have hc1_eq : d.cell1 = (2, 3) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc1_row : d.cell1.2 = 2 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · have hc1_eq : d.cell1 = (1, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_12; left; exact hc1_eq.symm
      · have hc1_eq : d.cell1 = (3, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]

/-- If a domino d covers (2, 3), is contained in Rectangle n 3 (n ≥ 3), and
    doesn't cover (1, 3), then d.cells is one of:
    - {(2, 3), (3, 3)} (horizontal going right)
    - {(2, 2), (2, 3)} (vertical going down) -/

lemma domino_at_23_options (n : ℕ) (d : Domino)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (2, 3) ∈ d.cells)
    (h_not_13 : (1, 3) ∉ d.cells) :
    d.cells = {(2, 3), (3, 3)} ∨ d.cells = {(2, 2), (2, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_13 ⊢
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · have hc1_eq : d.cell1 = (2, 3) := hc1.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc2_col : d.cell2.1 = 2 := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · exfalso
        have hc2_row : d.cell2.2 = 4 := by rw [hc1_eq] at h; omega
        omega
      · have hc2_eq : d.cell2 = (2, 2) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc2_row : d.cell2.2 = 3 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · have hc2_eq : d.cell2 = (3, 3) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        left; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (1, 3) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_13; right; exact hc2_eq.symm
  · have hc2_eq : d.cell2 = (2, 3) := hc2.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc1_col : d.cell1.1 = 2 := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · have hc1_eq : d.cell1 = (2, 2) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; simp only [hc1_eq, hc2_eq]
      · exfalso
        have hc1_row : d.cell1.2 = 4 := by rw [hc2_eq] at h; omega
        omega
    · have hc1_row : d.cell1.2 = 3 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · have hc1_eq : d.cell1 = (1, 3) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_13; left; exact hc1_eq.symm
      · have hc1_eq : d.cell1 = (3, 3) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]

/-- Helper: If d.cells = {(1, 1), (2, 1)}, then d.maxCol = 2. -/
lemma maxCol_eq_2_of_cells_eq_11_21 (d : Domino) (h : d.cells = {(1, 1), (2, 1)}) :
    d.maxCol = 2 := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(1, 1), (2, 1)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(1, 1), (2, 1)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

/-- Helper: If d.cells = {(2, 2), (2, 3)}, then d.minCol = d.maxCol = 2. -/
lemma minCol_maxCol_eq_2_of_cells_eq_22_23 (d : Domino) (h : d.cells = {(2, 2), (2, 3)}) :
    d.minCol = 2 ∧ d.maxCol = 2 := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(2, 2), (2, 3)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(2, 2), (2, 3)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.minCol, Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

/-- Helper: If d.cells = {(2, 1), (2, 2)}, then d.minCol = d.maxCol = 2. -/
lemma minCol_maxCol_eq_2_of_cells_eq_21_22 (d : Domino) (h : d.cells = {(2, 1), (2, 2)}) :
    d.minCol = 2 ∧ d.maxCol = 2 := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(2, 1), (2, 2)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(2, 1), (2, 2)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.minCol, Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

/-- If a domino d covers (c, 1), is contained in Rectangle n 3, and
    doesn't cover (c-1, 1) or (c, 2), then d.cells = {(c, 1), (c+1, 1)}.
    This is the "forced right" lemma for row 1. -/

lemma domino_at_c1_forced_right (n c : ℕ) (d : Domino)
    (_hc_ge : c ≥ 1) (_hc_lt : c < n)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (c, 1) ∈ d.cells)
    (h_not_left : (c - 1, 1) ∉ d.cells) (h_not_up : (c, 2) ∉ d.cells) :
    d.cells = {(c, 1), (c + 1, 1)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_left h_not_up
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · -- (c, 1) = d.cell1
    have hc1_eq : d.cell1 = (c, 1) := hc1.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · -- vertical domino: columns equal
      have hc2_col : d.cell2.1 = c := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · -- d.cell1.2 + 1 = d.cell2.2, so d.cell2 = (c, 2)
        have hc2_eq : d.cell2 = (c, 2) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        exfalso; apply h_not_up; right; exact hc2_eq.symm
      · -- d.cell2.2 + 1 = d.cell1.2, so d.cell2 = (c, 0)
        have hc2_row : d.cell2.2 = 0 := by rw [hc1_eq] at h; omega
        omega -- contradicts hd_c2_in.2.2.1 (row ≥ 1)
    · -- horizontal domino: rows equal
      have hc2_row : d.cell2.2 = 1 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · -- d.cell1.1 + 1 = d.cell2.1, so d.cell2 = (c + 1, 1)
        have hc2_eq : d.cell2 = (c + 1, 1) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        simp only [Domino.cells, hc1_eq, hc2_eq]
      · -- d.cell2.1 + 1 = d.cell1.1, so d.cell2 = (c - 1, 1)
        have hc2_eq : d.cell2 = (c - 1, 1) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_left; right; exact hc2_eq.symm
  · -- (c, 1) = d.cell2, symmetric case
    have hc2_eq : d.cell2 = (c, 1) := hc2.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · -- vertical domino
      have hc1_col : d.cell1.1 = c := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · -- d.cell1.2 + 1 = d.cell2.2, so d.cell1 = (c, 0)
        have hc1_row : d.cell1.2 = 0 := by rw [hc2_eq] at h; omega
        omega -- contradicts hd_c1_in.2.2.1
      · -- d.cell2.2 + 1 = d.cell1.2, so d.cell1 = (c, 2)
        have hc1_eq : d.cell1 = (c, 2) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        exfalso; apply h_not_up; left; exact hc1_eq.symm
    · -- horizontal domino
      have hc1_row : d.cell1.2 = 1 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · -- d.cell1.1 + 1 = d.cell2.1, so d.cell1 = (c - 1, 1)
        have hc1_eq : d.cell1 = (c - 1, 1) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_left; left; exact hc1_eq.symm
      · -- d.cell2.1 + 1 = d.cell1.1, so d.cell1 = (c + 1, 1)
        have hc1_eq : d.cell1 = (c + 1, 1) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        simp only [Domino.cells, hc1_eq, hc2_eq, Finset.pair_comm]

/-- If a domino d covers (c, 2), is contained in Rectangle n 3, and
    doesn't cover (c-1, 2), then d.cells is one of:
    - {(c, 2), (c+1, 2)} (horizontal going right)
    - {(c, 1), (c, 2)} (vertical going down)
    - {(c, 2), (c, 3)} (vertical going up) -/

lemma domino_at_c2_options (n c : ℕ) (d : Domino)
    (_hc_ge : c ≥ 1) (_hc_lt : c < n)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (c, 2) ∈ d.cells)
    (h_not_left : (c - 1, 2) ∉ d.cells) :
    d.cells = {(c, 2), (c + 1, 2)} ∨ d.cells = {(c, 1), (c, 2)} ∨ d.cells = {(c, 2), (c, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_left ⊢
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · have hc1_eq : d.cell1 = (c, 2) := hc1.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc2_col : d.cell2.1 = c := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · have hc2_eq : d.cell2 = (c, 3) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (c, 1) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc2_row : d.cell2.2 = 2 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · have hc2_eq : d.cell2 = (c + 1, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        left; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (c - 1, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_left; right; exact hc2_eq.symm
  · have hc2_eq : d.cell2 = (c, 2) := hc2.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc1_col : d.cell1.1 = c := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · have hc1_eq : d.cell1 = (c, 1) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq]
      · have hc1_eq : d.cell1 = (c, 3) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc1_row : d.cell1.2 = 2 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · have hc1_eq : d.cell1 = (c - 1, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_left; left; exact hc1_eq.symm
      · have hc1_eq : d.cell1 = (c + 1, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]

/-- If a domino d covers (c, 3), is contained in Rectangle n 3, and
    doesn't cover (c-1, 3), then d.cells is one of:
    - {(c, 3), (c+1, 3)} (horizontal going right)
    - {(c, 2), (c, 3)} (vertical going down) -/

lemma domino_at_c3_options (n c : ℕ) (d : Domino)
    (_hc_ge : c ≥ 1) (_hc_lt : c < n)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (c, 3) ∈ d.cells)
    (h_not_left : (c - 1, 3) ∉ d.cells) :
    d.cells = {(c, 3), (c + 1, 3)} ∨ d.cells = {(c, 2), (c, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_left ⊢
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  rcases h_cov with hc1 | hc2
  · have hc1_eq : d.cell1 = (c, 3) := hc1.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc2_col : d.cell2.1 = c := by rw [← hcol, hc1_eq]
      rcases hrow with h | h
      · exfalso
        have hc2_row : d.cell2.2 = 4 := by rw [hc1_eq] at h; omega
        omega
      · have hc2_eq : d.cell2 = (c, 2) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc2_row : d.cell2.2 = 3 := by rw [← hrow, hc1_eq]
      rcases hcol with h | h
      · have hc2_eq : d.cell2 = (c + 1, 3) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        left; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (c - 1, 3) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_left; right; exact hc2_eq.symm
  · have hc2_eq : d.cell2 = (c, 3) := hc2.symm
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · have hc1_col : d.cell1.1 = c := by rw [hcol, hc2_eq]
      rcases hrow with h | h
      · have hc1_eq : d.cell1 = (c, 2) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; simp only [hc1_eq, hc2_eq]
      · exfalso
        have hc1_row : d.cell1.2 = 4 := by rw [hc2_eq] at h; omega
        omega
    · have hc1_row : d.cell1.2 = 3 := by rw [hrow, hc2_eq]
      rcases hcol with h | h
      · have hc1_eq : d.cell1 = (c - 1, 3) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_left; left; exact hc1_eq.symm
      · have hc1_eq : d.cell1 = (c + 1, 3) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]

/-- Helper: If d.cells = {(c, 2), (c, 3)}, then d.minCol = d.maxCol = c. -/
lemma minCol_maxCol_eq_c_of_cells_eq_c2_c3 (c : ℕ) (d : Domino) (h : d.cells = {(c, 2), (c, 3)}) :
    d.minCol = c ∧ d.maxCol = c := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(c, 2), (c, 3)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(c, 2), (c, 3)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.minCol, Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

/-- Helper: If d.cells = {(c, 1), (c, 2)}, then d.minCol = d.maxCol = c. -/
lemma minCol_maxCol_eq_c_of_cells_eq_c1_c2 (c : ℕ) (d : Domino) (h : d.cells = {(c, 1), (c, 2)}) :
    d.minCol = c ∧ d.maxCol = c := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(c, 1), (c, 2)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(c, 1), (c, 2)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.minCol, Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

/-- Helper: If d.cells = {(c, 1), (c+1, 1)}, then d.maxCol = c+1. -/
lemma maxCol_eq_c_add_1_of_cells_eq_c1_c_add_1_1 (c : ℕ) (d : Domino) (h : d.cells = {(c, 1), (c + 1, 1)}) :
    d.maxCol = c + 1 := by
  simp only [Domino.cells] at h
  have h1 : d.cell1 ∈ ({(c, 1), (c + 1, 1)} : Finset Cell) := by rw [← h]; simp
  have h2 : d.cell2 ∈ ({(c, 1), (c + 1, 1)} : Finset Cell) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  simp only [Domino.maxCol]
  rcases h1 with hc1 | hc1 <;> rcases h2 with hc2 | hc2
  · exfalso; exact d.distinct (hc1.trans hc2.symm)
  · simp [hc1, hc2]
  · simp [hc1, hc2]
  · exfalso; exact d.distinct (hc1.trans hc2.symm)

/-- Claim 1 from the proof: For each positive integer i < n/2, a faultfree tiling T
    with a vertical domino in the top of column 1 must contain specific dominos.

    Note: We use `d.cells` (the set of cells covered by the domino) instead of specifying
    cell orderings, since the `Domino` structure allows either cell to be `cell1` or `cell2`.
    This makes the theorem provable for arbitrary tilings.

    This is proved by induction on i. -/

lemma claim1_basement_middle_top (n : ℕ) (T : DominoTiling n 3)
    (hfree : T.isFaultfree) (htop : T.hasTopVerticalInCol 1)
    (i : ℕ) (hi_pos : i ≥ 1) (hi_lt : i < n / 2) :
    -- T contains the basement domino covering cells {(2i-1, 1), (2i, 1)}
    (∃ d ∈ T.dominos, d.cells = {(2*i - 1, 1), (2*i, 1)}) ∧
    -- T contains the middle domino covering cells {(2i, 2), (2i+1, 2)}
    (∃ d ∈ T.dominos, d.cells = {(2*i, 2), (2*i + 1, 2)}) ∧
    -- T contains the top domino covering cells {(2i, 3), (2i+1, 3)}
    (∃ d ∈ T.dominos, d.cells = {(2*i, 3), (2*i + 1, 3)}) := by
  -- The proof is by strong induction on i.
  -- For each i with 1 ≤ i < n/2, we prove:
  -- 1. T contains basement domino: cell1 = (2i-1, 1), cell2 = (2i, 1)
  -- 2. T contains middle domino: cell1 = (2i, 2), cell2 = (2i+1, 2)
  -- 3. T contains top domino: cell1 = (2i, 3), cell2 = (2i+1, 3)
  --
  -- Base case (i=1):
  -- - htop gives us a vertical domino in col 1 covering rows 2-3
  -- - Cell (1,1) must be covered by some domino d
  -- - d can't be vertical (col 1 rows 2-3 already covered)
  -- - d must be horizontal going right: {(1,1), (2,1)}
  -- - This is the basement domino for i=1
  -- - Now (2,2) and (2,3) must be covered
  -- - If by vertical domino in col 2, then col 2 would end at maxCol=2
  -- - But basement also ends at maxCol=2, creating fault at col 2
  -- - So (2,2) and (2,3) are covered by horizontal dominos going right
  -- - These are the middle and top dominos for i=1
  --
  -- Induction step (j → j+1):
  -- - By IH: basement at (2j-1,1)-(2j,1), middle at (2j,2)-(2j+1,2), top at (2j,3)-(2j+1,3)
  -- - Cell (2j+1, 1) must be covered
  -- - Can't be vertical (would collide with middle domino at (2j+1, 2))
  -- - Can't be horizontal going left (would collide with basement at (2j, 1))
  -- - Must be horizontal going right: {(2j+1, 1), (2j+2, 1)} - basement for j+1
  -- - Now (2j+2, 2) and (2j+2, 3) must be covered
  -- - If by vertical in col 2j+2, then fault at col 2j+2 (basement ends there too)
  -- - So horizontal going right: middle and top for j+1
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_or_lt_of_le hi_pos with hi_eq | hi_gt
    · -- Base case: i = 1
      subst hi_eq
      simp only [Nat.mul_one, Nat.reduceSubDiff]
      -- From hi_lt : 1 < n / 2, we get n ≥ 4
      have hn_ge_2 : n ≥ 2 := by omega
      -- Get basement domino from base_case_basement
      obtain ⟨d_base, hd_base_mem, hd_base_cells⟩ := base_case_basement n T htop hn_ge_2
      -- Get the top vertical domino info
      obtain ⟨d_top, hd_top_mem, hd_top_vert, hd_top_col, hd_top_rows⟩ := htop
      -- The top vertical covers (1, 2) and (1, 3)
      have hd_top_c2_col : d_top.cell2.1 = 1 := hd_top_vert.symm.trans hd_top_col
      have hd_top_covers_12 : (1, 2) ∈ d_top.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        rcases hd_top_rows with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
        · left; ext; exact hd_top_col.symm; omega
        · right; ext; exact hd_top_c2_col.symm; omega
      have hd_top_covers_13 : (1, 3) ∈ d_top.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        rcases hd_top_rows with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
        · right; ext; exact hd_top_c2_col.symm; omega
        · left; ext; exact hd_top_col.symm; omega
      -- Cell (2, 2) must be covered by some domino d_mid
      have h22_in : (2, 2) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_mid, hd_mid_mem, hd_mid_cov⟩ := T.cell_covered (2, 2) h22_in
      -- d_mid doesn't cover (1, 2) (that's covered by d_top)
      have hd_mid_ne_top : d_mid ≠ d_top := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd_mid_cov
        rcases hd_mid_cov with h | h
        · have hcol : d_mid.cell1.1 = 2 := by rw [← h]
          rw [hd_top_col] at hcol
          omega
        · have hcol : d_mid.cell2.1 = 2 := by rw [← h]
          rw [hd_top_c2_col] at hcol
          omega
      have hd_mid_not_12 : (1, 2) ∉ d_mid.cells := by
        intro h12
        have heq := T.cell_covered_unique (1, 2) d_mid d_top hd_mid_mem hd_top_mem h12 hd_top_covers_12
        exact hd_mid_ne_top heq
      -- The middle domino must be horizontal going right: {(2,2), (3,2)}
      -- (vertical would create fault at col 2, horizontal left blocked by top vertical at (1,2))
      have hd_mid_cells : d_mid.cells = {(2, 2), (3, 2)} := by
        have hn_ge_3 : n ≥ 3 := by omega
        have hd_mid_in_rect := T.dominos_in_rect d_mid hd_mid_mem
        have h_opts := domino_at_22_options n d_mid hd_mid_in_rect hd_mid_cov hd_mid_not_12
        rcases h_opts with h_horiz | h_vert_down | h_vert_up
        · exact h_horiz
        · -- Case {(2, 1), (2, 2)}: d_mid covers (2, 1), but d_base also covers (2, 1)
          exfalso
          have h21_in_mid : (2, 1) ∈ d_mid.cells := by rw [h_vert_down]; simp
          have h21_in_base : (2, 1) ∈ d_base.cells := by rw [hd_base_cells]; simp
          have heq := T.cell_covered_unique (2, 1) d_mid d_base hd_mid_mem hd_base_mem h21_in_mid h21_in_base
          rw [heq, hd_base_cells] at h_vert_down
          have : (2, 2) ∈ ({(1, 1), (2, 1)} : Finset Cell) := by rw [h_vert_down]; simp
          simp at this
        · -- Case {(2, 2), (2, 3)}: Creates fault at column 2
          exfalso
          -- Show that no domino in T spans column 2
          have hfault : T.hasFaultAt 2 := by
            constructor
            · omega
            constructor
            · omega
            intro d hd_mem' ⟨hmin, hmax⟩
            -- d spans column 2, so it has a cell in column 2 with maxCol ≥ 3
            -- The cells in column 2 are (2,1), (2,2), (2,3)
            -- (2,1) is covered by d_base with maxCol = 2
            -- (2,2) and (2,3) are covered by d_mid with maxCol = 2
            -- So d must be one of d_base or d_mid, both have maxCol = 2, contradiction
            have hd_maxCol_ge_3 : d.maxCol ≥ 3 := by omega
            -- d has minCol ≤ 2 and maxCol ≥ 3, so d is horizontal spanning columns 2-3
            -- This means d has a cell in column 2
            have hd_col2_cell : ∃ r, (2, r) ∈ d.cells := by
              -- Since minCol ≤ 2 and maxCol ≥ 3, and dominos are adjacent pairs,
              -- the domino must have one cell with column 2 and one with column 3
              have hd_horiz : d.isHorizontal := by
                unfold Domino.isHorizontal
                rcases d.adjacent with ⟨hcol, _⟩ | ⟨hrow, _⟩
                · -- vertical: minCol = maxCol, but we have minCol ≤ 2 < 3 ≤ maxCol
                  simp only [Domino.minCol, Domino.maxCol] at hmin hmax
                  have : d.cell1.1 = d.cell2.1 := hcol
                  omega
                · exact hrow
              -- d is horizontal with minCol ≤ 2 < maxCol
              simp only [Domino.minCol, Domino.maxCol] at hmin hmax
              -- Since d is horizontal and adjacent, |cell1.1 - cell2.1| = 1
              have hadj : d.cell1.1 + 1 = d.cell2.1 ∨ d.cell2.1 + 1 = d.cell1.1 := by
                rcases d.adjacent with ⟨hvert, _⟩ | ⟨_, hcol⟩
                · -- vertical case: contradicts that d is horizontal
                  exfalso
                  simp only [Domino.isHorizontal] at hd_horiz
                  -- hvert says columns are equal, but hmin ≤ 2 < hmax means columns differ
                  omega
                · exact hcol
              have hc1_or_c2 : d.cell1.1 = 2 ∨ d.cell2.1 = 2 := by
                rcases hadj with h | h
                · -- d.cell1.1 + 1 = d.cell2.1
                  have ha_le : d.cell1.1 ≤ 2 := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have hb_gt : d.cell2.1 > 2 := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  left; omega
                · -- d.cell2.1 + 1 = d.cell1.1
                  have hb_le : d.cell2.1 ≤ 2 := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have ha_gt : d.cell1.1 > 2 := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  right; omega
              rcases hc1_or_c2 with hc1 | hc2
              · have heq : (2, d.cell1.2) = d.cell1 := by ext <;> simp [hc1]
                exact ⟨d.cell1.2, by simp [Domino.cells, heq]⟩
              · have heq : (2, d.cell2.2) = d.cell2 := by ext <;> simp [hc2]
                exact ⟨d.cell2.2, by simp [Domino.cells, heq]⟩
            obtain ⟨r, hr_in⟩ := hd_col2_cell
            -- (2, r) is in column 2, so r ∈ {1, 2, 3}
            have hd_in_rect := T.dominos_in_rect d hd_mem'
            have h2r_in_rect : (2, r) ∈ Rectangle n 3 := hd_in_rect hr_in
            rw [mem_Rectangle] at h2r_in_rect
            have hr_range : r = 1 ∨ r = 2 ∨ r = 3 := by omega
            rcases hr_range with hr1 | hr2 | hr3
            · -- (2, 1) is covered by d_base
              subst hr1
              have heq := T.cell_covered_unique (2, 1) d d_base hd_mem' hd_base_mem hr_in
                (by rw [hd_base_cells]; simp)
              rw [heq] at hd_maxCol_ge_3
              have hbase_max : d_base.maxCol = 2 := maxCol_eq_2_of_cells_eq_11_21 d_base hd_base_cells
              omega
            · -- (2, 2) is covered by d_mid
              subst hr2
              have heq := T.cell_covered_unique (2, 2) d d_mid hd_mem' hd_mid_mem hr_in hd_mid_cov
              rw [heq] at hd_maxCol_ge_3
              have hmid_minmax := minCol_maxCol_eq_2_of_cells_eq_22_23 d_mid h_vert_up
              omega
            · -- (2, 3) is covered by d_mid (since d_mid = {(2,2), (2,3)})
              subst hr3
              have h23_in_mid : (2, 3) ∈ d_mid.cells := by rw [h_vert_up]; simp
              have heq := T.cell_covered_unique (2, 3) d d_mid hd_mem' hd_mid_mem hr_in h23_in_mid
              rw [heq] at hd_maxCol_ge_3
              have hmid_minmax := minCol_maxCol_eq_2_of_cells_eq_22_23 d_mid h_vert_up
              omega
          -- But T is faultfree
          exact hfree 2 (by omega) (by omega) hfault
      -- Similarly for top domino covering (2, 3)
      have h23_in : (2, 3) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_top', hd_top'_mem, hd_top'_cov⟩ := T.cell_covered (2, 3) h23_in
      have hd_top'_ne_top : d_top' ≠ d_top := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd_top'_cov
        rcases hd_top'_cov with h | h
        · have hcol : d_top'.cell1.1 = 2 := by rw [← h]
          rw [hd_top_col] at hcol
          omega
        · have hcol : d_top'.cell2.1 = 2 := by rw [← h]
          rw [hd_top_c2_col] at hcol
          omega
      have hd_top'_not_13 : (1, 3) ∉ d_top'.cells := by
        intro h13
        have heq := T.cell_covered_unique (1, 3) d_top' d_top hd_top'_mem hd_top_mem h13 hd_top_covers_13
        exact hd_top'_ne_top heq
      have hd_top'_cells : d_top'.cells = {(2, 3), (3, 3)} := by
        have hd_top'_in_rect := T.dominos_in_rect d_top' hd_top'_mem
        have h_opts := domino_at_23_options n d_top' hd_top'_in_rect hd_top'_cov hd_top'_not_13
        rcases h_opts with h_horiz | h_vert
        · exact h_horiz
        · -- Case {(2, 2), (2, 3)}: d_top' covers (2, 2), but d_mid also covers (2, 2)
          -- So d_top' = d_mid, but d_mid.cells = {(2, 2), (3, 2)} ≠ {(2, 2), (2, 3)}
          exfalso
          have h22_in_top' : (2, 2) ∈ d_top'.cells := by rw [h_vert]; simp
          have heq := T.cell_covered_unique (2, 2) d_top' d_mid hd_top'_mem hd_mid_mem h22_in_top' hd_mid_cov
          rw [heq, hd_mid_cells] at h_vert
          have : (2, 3) ∈ ({(2, 2), (3, 2)} : Finset Cell) := by rw [h_vert]; simp
          simp at this
      exact ⟨⟨d_base, hd_base_mem, hd_base_cells⟩,
             ⟨d_mid, hd_mid_mem, hd_mid_cells⟩,
             ⟨d_top', hd_top'_mem, hd_top'_cells⟩⟩
    · -- Induction step: i > 1
      have hi_pred_pos : i - 1 ≥ 1 := by omega
      have hi_pred_lt : i - 1 < n / 2 := by omega
      have hi_pred_lt_i : i - 1 < i := by omega
      have ih_result := ih (i - 1) hi_pred_lt_i hi_pred_pos hi_pred_lt
      obtain ⟨⟨d_base_prev, hd_base_prev_mem, hd_base_prev_cells⟩,
              ⟨d_mid_prev, hd_mid_prev_mem, hd_mid_prev_cells⟩,
              ⟨d_top_prev, hd_top_prev_mem, hd_top_prev_cells⟩⟩ := ih_result
      -- The induction step follows the same pattern as the base case
      -- Cell (2i-1, 1) must be covered by a horizontal domino going right
      -- (going left collides with basement from i-1, vertical collides with middle from i-1)
      -- Then (2i, 2) and (2i, 3) must be horizontal going right by faultfreeness
      
      -- Simplify the IH cells using the fact that i ≥ 2
      have hi_ge_2 : i ≥ 2 := by omega
      have h_sub_add : 2 * i - 2 + 1 = 2 * i - 1 := by omega
      have hprev_base_simp : d_base_prev.cells = {(2*i - 3, 1), (2*i - 2, 1)} := by
        simp only [Nat.mul_sub_one, Nat.sub_sub] at hd_base_prev_cells
        norm_num at hd_base_prev_cells
        exact hd_base_prev_cells
      have hprev_mid_simp : d_mid_prev.cells = {(2*i - 2, 2), (2*i - 1, 2)} := by
        simp only [Nat.mul_sub_one] at hd_mid_prev_cells
        simp only [h_sub_add] at hd_mid_prev_cells
        exact hd_mid_prev_cells
      have hprev_top_simp : d_top_prev.cells = {(2*i - 2, 3), (2*i - 1, 3)} := by
        simp only [Nat.mul_sub_one] at hd_top_prev_cells
        simp only [h_sub_add] at hd_top_prev_cells
        exact hd_top_prev_cells
      
      -- Cell (2i-1, 1) must be covered by some domino d_base
      have h_cell_base_in : (2*i - 1, 1) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_base, hd_base_mem, hd_base_cov⟩ := T.cell_covered (2*i - 1, 1) h_cell_base_in
      
      -- d_base can't cover (2i-2, 1) - that's in d_base_prev
      have hd_base_not_left : (2*i - 2, 1) ∉ d_base.cells := by
        intro h_in_base
        have h_in_prev : (2*i - 2, 1) ∈ d_base_prev.cells := by rw [hprev_base_simp]; simp
        have heq := T.cell_covered_unique (2*i - 2, 1) d_base d_base_prev hd_base_mem hd_base_prev_mem h_in_base h_in_prev
        rw [heq, hprev_base_simp] at hd_base_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_base_cov
        rcases hd_base_cov with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      
      -- d_base can't cover (2i-1, 2) - that's in d_mid_prev
      have hd_base_not_up : (2*i - 1, 2) ∉ d_base.cells := by
        intro h_in_base
        have h_in_prev : (2*i - 1, 2) ∈ d_mid_prev.cells := by rw [hprev_mid_simp]; simp
        have heq := T.cell_covered_unique (2*i - 1, 2) d_base d_mid_prev hd_base_mem hd_mid_prev_mem h_in_base h_in_prev
        rw [heq, hprev_mid_simp] at hd_base_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_base_cov
        rcases hd_base_cov with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      
      -- By domino_at_c1_forced_right, d_base must go right
      have hd_base_in_rect := T.dominos_in_rect d_base hd_base_mem
      have hc_ge : 2*i - 1 ≥ 1 := by omega
      have hc_lt : 2*i - 1 < n := by omega
      -- Adjust the cell coordinates for the lemma
      have hd_base_cov' : (2*i - 1, 1) ∈ d_base.cells := hd_base_cov
      have hd_base_not_left' : (2*i - 1 - 1, 1) ∉ d_base.cells := by
        simp only [Nat.sub_sub]; exact hd_base_not_left
      have hd_base_not_up' : (2*i - 1, 2) ∉ d_base.cells := hd_base_not_up
      have hd_base_cells := domino_at_c1_forced_right n (2*i - 1) d_base hc_ge hc_lt 
        hd_base_in_rect hd_base_cov' hd_base_not_left' hd_base_not_up'
      -- Convert back to the form we need
      have hd_base_cells' : d_base.cells = {(2*i - 1, 1), (2*i, 1)} := by
        simp only [Nat.sub_add_cancel (by omega : 2*i ≥ 1)] at hd_base_cells
        exact hd_base_cells
      
      -- Now for the middle domino covering (2i, 2)
      have h_cell_mid_in : (2*i, 2) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_mid, hd_mid_mem, hd_mid_cov⟩ := T.cell_covered (2*i, 2) h_cell_mid_in
      
      -- d_mid can't cover (2i-1, 2) - that's in d_mid_prev
      have hd_mid_not_left : (2*i - 1, 2) ∉ d_mid.cells := by
        intro h_in_mid
        have h_in_prev : (2*i - 1, 2) ∈ d_mid_prev.cells := by rw [hprev_mid_simp]; simp
        have heq := T.cell_covered_unique (2*i - 1, 2) d_mid d_mid_prev hd_mid_mem hd_mid_prev_mem h_in_mid h_in_prev
        rw [heq, hprev_mid_simp] at hd_mid_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_mid_cov
        rcases hd_mid_cov with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      
      -- Use domino_at_c2_options to classify d_mid
      have hd_mid_in_rect := T.dominos_in_rect d_mid hd_mid_mem
      have hc_mid_ge : 2*i ≥ 1 := by omega
      have hc_mid_lt : 2*i < n := by omega
      have hd_mid_not_left' : (2*i - 1, 2) ∉ d_mid.cells := hd_mid_not_left
      have h_mid_opts := domino_at_c2_options n (2*i) d_mid hc_mid_ge hc_mid_lt 
        hd_mid_in_rect hd_mid_cov hd_mid_not_left'
      
      have hd_mid_cells : d_mid.cells = {(2*i, 2), (2*i + 1, 2)} := by
        rcases h_mid_opts with h_horiz | h_vert_down | h_vert_up
        · exact h_horiz
        · -- Case {(2i, 1), (2i, 2)}: d_mid covers (2i, 1), but d_base also covers (2i, 1)
          exfalso
          have h_in_mid : (2*i, 1) ∈ d_mid.cells := by rw [h_vert_down]; simp
          have h_in_base : (2*i, 1) ∈ d_base.cells := by rw [hd_base_cells']; simp
          have heq := T.cell_covered_unique (2*i, 1) d_mid d_base hd_mid_mem hd_base_mem h_in_mid h_in_base
          rw [heq, hd_base_cells'] at h_vert_down
          have hmem : (2*i, 2) ∈ ({(2*i - 1, 1), (2*i, 1)} : Finset Cell) := by rw [h_vert_down]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        · -- Case {(2i, 2), (2i, 3)}: Creates fault at column 2i
          exfalso
          -- Show that no domino in T spans column 2i
          have hfault : T.hasFaultAt (2*i) := by
            constructor
            · omega
            constructor
            · omega
            intro d hd_mem' ⟨hmin, hmax⟩
            have hd_maxCol_ge : d.maxCol ≥ 2*i + 1 := by omega
            -- d has minCol ≤ 2i and maxCol ≥ 2i+1, so d is horizontal spanning columns 2i and 2i+1
            have hd_col_cell : ∃ r, (2*i, r) ∈ d.cells := by
              have hd_horiz : d.isHorizontal := by
                unfold Domino.isHorizontal
                rcases d.adjacent with ⟨hcol, _⟩ | ⟨hrow, _⟩
                · simp only [Domino.minCol, Domino.maxCol] at hmin hmax
                  have : d.cell1.1 = d.cell2.1 := hcol
                  omega
                · exact hrow
              simp only [Domino.minCol, Domino.maxCol] at hmin hmax
              have hadj : d.cell1.1 + 1 = d.cell2.1 ∨ d.cell2.1 + 1 = d.cell1.1 := by
                rcases d.adjacent with ⟨hvert, _⟩ | ⟨_, hcol⟩
                · exfalso; simp only [Domino.isHorizontal] at hd_horiz; omega
                · exact hcol
              have hc1_or_c2 : d.cell1.1 = 2*i ∨ d.cell2.1 = 2*i := by
                rcases hadj with h | h
                · have ha_le : d.cell1.1 ≤ 2*i := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have hb_gt : d.cell2.1 > 2*i := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  left; omega
                · have hb_le : d.cell2.1 ≤ 2*i := by simp only [min_def] at hmin; split_ifs at hmin <;> omega
                  have ha_gt : d.cell1.1 > 2*i := by simp only [max_def] at hmax; split_ifs at hmax <;> omega
                  right; omega
              rcases hc1_or_c2 with hc1 | hc2
              · have heq : (2*i, d.cell1.2) = d.cell1 := by ext <;> simp [hc1]
                exact ⟨d.cell1.2, by simp [Domino.cells, heq]⟩
              · have heq : (2*i, d.cell2.2) = d.cell2 := by ext <;> simp [hc2]
                exact ⟨d.cell2.2, by simp [Domino.cells, heq]⟩
            obtain ⟨r, hr_in⟩ := hd_col_cell
            have hd_in_rect := T.dominos_in_rect d hd_mem'
            have h_in_rect : (2*i, r) ∈ Rectangle n 3 := hd_in_rect hr_in
            rw [mem_Rectangle] at h_in_rect
            have hr_range : r = 1 ∨ r = 2 ∨ r = 3 := by omega
            rcases hr_range with hr1 | hr2 | hr3
            · -- (2i, 1) is covered by d_base
              subst hr1
              have heq := T.cell_covered_unique (2*i, 1) d d_base hd_mem' hd_base_mem hr_in
                (by rw [hd_base_cells']; simp)
              rw [heq] at hd_maxCol_ge
              have hbase_max := maxCol_eq_c_add_1_of_cells_eq_c1_c_add_1_1 (2*i - 1) d_base hd_base_cells
              omega
            · -- (2i, 2) is covered by d_mid
              subst hr2
              have heq := T.cell_covered_unique (2*i, 2) d d_mid hd_mem' hd_mid_mem hr_in hd_mid_cov
              rw [heq] at hd_maxCol_ge
              have hmid_minmax := minCol_maxCol_eq_c_of_cells_eq_c2_c3 (2*i) d_mid h_vert_up
              omega
            · -- (2i, 3) is covered by d_mid (since d_mid = {(2i, 2), (2i, 3)})
              subst hr3
              have h_in_mid : (2*i, 3) ∈ d_mid.cells := by rw [h_vert_up]; simp
              have heq := T.cell_covered_unique (2*i, 3) d d_mid hd_mem' hd_mid_mem hr_in h_in_mid
              rw [heq] at hd_maxCol_ge
              have hmid_minmax := minCol_maxCol_eq_c_of_cells_eq_c2_c3 (2*i) d_mid h_vert_up
              omega
          -- But T is faultfree
          exact hfree (2*i) (by omega) (by omega) hfault
      
      -- Now for the top domino covering (2i, 3)
      have h_cell_top_in : (2*i, 3) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_top', hd_top'_mem, hd_top'_cov⟩ := T.cell_covered (2*i, 3) h_cell_top_in
      
      -- d_top' can't cover (2i-1, 3) - that's in d_top_prev
      have hd_top'_not_left : (2*i - 1, 3) ∉ d_top'.cells := by
        intro h_in_top'
        have h_in_prev : (2*i - 1, 3) ∈ d_top_prev.cells := by rw [hprev_top_simp]; simp
        have heq := T.cell_covered_unique (2*i - 1, 3) d_top' d_top_prev hd_top'_mem hd_top_prev_mem h_in_top' h_in_prev
        rw [heq, hprev_top_simp] at hd_top'_cov
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_top'_cov
        rcases hd_top'_cov with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      
      -- Use domino_at_c3_options to classify d_top'
      have hd_top'_in_rect := T.dominos_in_rect d_top' hd_top'_mem
      have h_top_opts := domino_at_c3_options n (2*i) d_top' hc_mid_ge hc_mid_lt 
        hd_top'_in_rect hd_top'_cov hd_top'_not_left
      
      have hd_top'_cells : d_top'.cells = {(2*i, 3), (2*i + 1, 3)} := by
        rcases h_top_opts with h_horiz | h_vert
        · exact h_horiz
        · -- Case {(2i, 2), (2i, 3)}: d_top' covers (2i, 2), but d_mid also covers (2i, 2)
          exfalso
          have h_in_top' : (2*i, 2) ∈ d_top'.cells := by rw [h_vert]; simp
          have heq := T.cell_covered_unique (2*i, 2) d_top' d_mid hd_top'_mem hd_mid_mem h_in_top' hd_mid_cov
          rw [heq, hd_mid_cells] at h_vert
          have hmem : (2*i, 3) ∈ ({(2*i, 2), (2*i + 1, 2)} : Finset Cell) := by rw [h_vert]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmem
          rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      
      exact ⟨⟨d_base, hd_base_mem, hd_base_cells'⟩,
             ⟨d_mid, hd_mid_mem, hd_mid_cells⟩,
             ⟨d_top', hd_top'_mem, hd_top'_cells⟩⟩

/-- Claim 2 from the proof: The width n must be even.

    Alternative proof: Since T tiles R_{n,3} with dominos, the total number of squares
    (which is 3n) must be even. Hence n must be even. -/

lemma claim2_n_even (n : ℕ) (T : DominoTiling n 3)
    (_hfree : T.isFaultfree) (_htop : T.hasTopVerticalInCol 1) :
    Even n := by
  -- The rectangle R_{n,3} has 3n cells
  have h_card : (Rectangle n 3).card = n * 3 := card_Rectangle n 3
  -- The tiling covers all cells with dominos, so 3n = 2 * (number of dominos)
  have h_tiling : (Rectangle n 3).card = 2 * T.dominos.card := T.card_eq_twice_dominos
  -- Therefore n * 3 = 2 * T.dominos.card, so 2 | 3n
  rw [h_card] at h_tiling
  -- Since 2 | 3n and gcd(2,3) = 1, we have 2 | n
  have h_dvd : 2 ∣ n := by
    have h_coprime : Nat.Coprime 2 3 := by decide
    have h_dvd_3n : 2 ∣ 3 * n := ⟨T.dominos.card, by linarith⟩
    exact h_coprime.dvd_of_dvd_mul_left h_dvd_3n
  exact even_iff_two_dvd.mpr h_dvd

/-- A faultfree tiling with a vertical domino in the top of column 1 has n ≥ 2.
    This follows because n is even (from claim2_n_even) and n ≥ 1. -/

lemma faultfree_hasTopVerticalInCol_implies_n_ge_two (n : ℕ) (T : DominoTiling n 3)
    (hfree : T.isFaultfree) (htop : T.hasTopVerticalInCol 1) : n ≥ 2 := by
  have hn_even := claim2_n_even n T hfree htop
  have hn_ge_1 := hasTopVerticalInCol_implies_n_ge n T 1 htop
  obtain ⟨k, hk⟩ := hn_even
  omega

/-- If a domino d has (n, 3) ∈ d.cells and d.cells ⊆ Rectangle n 3, then
    d.cells = {(n-1, 3), (n, 3)} or d.cells = {(n, 2), (n, 3)}. -/

lemma domino_at_n3_options (n : ℕ) (d : Domino)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (n, 3) ∈ d.cells) :
    d.cells = {(n - 1, 3), (n, 3)} ∨ d.cells = {(n, 2), (n, 3)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov
  rcases h_cov with hc1 | hc2
  · have h2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [mem_Rectangle] at h2_in
    have hc1_col : d.cell1.1 = n := by rw [← hc1]
    have hc1_row : d.cell1.2 = 3 := by rw [← hc1]
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · right; simp only [Domino.cells]
      have hc2_col : d.cell2.1 = n := by rw [← hcol, hc1_col]
      rcases hrow with hr | hr
      · exfalso; omega
      · have hc2_row : d.cell2.2 = 2 := by omega
        have h2_eq : d.cell2 = (n, 2) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq, Finset.pair_comm]
    · left; simp only [Domino.cells]
      have hc2_row : d.cell2.2 = 3 := by rw [← hrow, hc1_row]
      rcases hcol with hc | hc
      · exfalso; omega
      · have hc2_col : d.cell2.1 = n - 1 := by omega
        have h2_eq : d.cell2 = (n - 1, 3) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq, Finset.pair_comm]
  · have h1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [mem_Rectangle] at h1_in
    have hc2_col : d.cell2.1 = n := by rw [← hc2]
    have hc2_row : d.cell2.2 = 3 := by rw [← hc2]
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · right; simp only [Domino.cells]
      have hc1_col : d.cell1.1 = n := by rw [hcol, hc2_col]
      rcases hrow with hr | hr
      · have hc1_row : d.cell1.2 = 2 := by omega
        have h1_eq : d.cell1 = (n, 2) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq]
      · exfalso; omega
    · left; simp only [Domino.cells]
      have hc1_row : d.cell1.2 = 3 := by rw [hrow, hc2_row]
      rcases hcol with hc | hc
      · have hc1_col : d.cell1.1 = n - 1 := by omega
        have h1_eq : d.cell1 = (n - 1, 3) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq]
      · exfalso; omega

/-- If a domino d has (n, 1) ∈ d.cells and d.cells ⊆ Rectangle n 3, then
    d.cells = {(n-1, 1), (n, 1)} or d.cells = {(n, 1), (n, 2)}. -/

lemma domino_at_n1_options (n : ℕ) (d : Domino)
    (h_in : d.cells ⊆ Rectangle n 3) (h_cov : (n, 1) ∈ d.cells) :
    d.cells = {(n - 1, 1), (n, 1)} ∨ d.cells = {(n, 1), (n, 2)} := by
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov
  rcases h_cov with hc1 | hc2
  · have h2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [mem_Rectangle] at h2_in
    have hc1_col : d.cell1.1 = n := by rw [← hc1]
    have hc1_row : d.cell1.2 = 1 := by rw [← hc1]
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · right; simp only [Domino.cells]
      have hc2_col : d.cell2.1 = n := by rw [← hcol, hc1_col]
      rcases hrow with hr | hr
      · have hc2_row : d.cell2.2 = 2 := by omega
        have h2_eq : d.cell2 = (n, 2) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq]
      · exfalso; omega
    · left; simp only [Domino.cells]
      have hc2_row : d.cell2.2 = 1 := by rw [← hrow, hc1_row]
      rcases hcol with hc | hc
      · exfalso; omega
      · have hc2_col : d.cell2.1 = n - 1 := by omega
        have h2_eq : d.cell2 = (n - 1, 1) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq, Finset.pair_comm]
  · have h1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [mem_Rectangle] at h1_in
    have hc2_col : d.cell2.1 = n := by rw [← hc2]
    have hc2_row : d.cell2.2 = 1 := by rw [← hc2]
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · right; simp only [Domino.cells]
      have hc1_col : d.cell1.1 = n := by rw [hcol, hc2_col]
      rcases hrow with hr | hr
      · exfalso; omega
      · have hc1_row : d.cell1.2 = 2 := by omega
        have h1_eq : d.cell1 = (n, 2) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq, Finset.pair_comm]
    · left; simp only [Domino.cells]
      have hc1_row : d.cell1.2 = 1 := by rw [hrow, hc2_row]
      rcases hcol with hc | hc
      · have hc1_col : d.cell1.1 = n - 1 := by omega
        have h1_eq : d.cell1 = (n - 1, 1) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq]
      · exfalso; omega

/-- (prop.gf.weighted-set.domino.Rn3.ABC (c))
    The only faultfree domino tiling of a height-3 rectangle with no vertical domino
    in the first column is equivalent to C.

    Proof sketch: If the first column has no vertical domino, it must be filled with
    three horizontal dominos extending into column 2. This forces n = 2, and the
    tiling must be equivalent to C.

    Note: We use TilingEquiv instead of = because the Domino structure distinguishes
    between {cell1 := (1, y), cell2 := (2, y)} and {cell1 := (2, y), cell2 := (1, y)}
    as different dominos, even though they cover the same cells. The mathematical
    theorem is about tilings covering the same cells, not about specific domino
    representations.

    Implementation note: The faultfree hypothesis `_hfree` is not used in this proof.
    In the source material, faultfree is used to argue there can't be a third column,
    but since this theorem is specifically for 2×3 rectangles (n = 2), this is automatic
    from the type signature. -/

lemma faultfree_no_vertical_unique (T : DominoTiling 2 3)
    (_hfree : T.isFaultfree) (hno_vert : ¬T.hasVerticalInCol 1) :
    DominoTiling.TilingEquiv T TilingC := by
  -- Strategy: Show every domino in T is horizontal, then the cells image matches TilingC
  -- Key insight: In a 2×3 rectangle with no vertical in column 1, all dominos must be horizontal
  -- because any vertical domino would have to be in column 1 or 2, and column 2 would force
  -- a horizontal domino to overlap with it.

  -- First, show every domino in T is horizontal
  have h_all_horiz : ∀ d ∈ T.dominos, d.isHorizontal := by
    intro d hd
    have h_in_rect := T.dominos_in_rect d hd
    -- A domino is either vertical or horizontal
    rcases d.adjacent with ⟨hcol, _⟩ | ⟨hrow, _⟩
    · -- Vertical case: d.cell1.1 = d.cell2.1
      exfalso
      -- d is vertical, so both cells are in the same column
      have hv : d.isVertical := hcol
      -- Get column bounds from rectangle membership
      have h1 : d.cell1 ∈ Rectangle 2 3 := h_in_rect (Finset.mem_insert_self _ _)
      rw [mem_Rectangle] at h1
      -- Column must be 1 or 2
      have hcol_bounds : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
      rcases hcol_bounds with hc | hc
      · -- Column 1: contradicts hno_vert
        apply hno_vert
        exact ⟨d, hd, hv, hc⟩
      · -- Column 2: Show this leads to contradiction
        -- d covers (2, r) and (2, r±1) for some r
        -- Cell (1, r) must be covered by some domino d' in T
        -- d' can't be vertical in column 1 (hypothesis)
        -- d' must be horizontal, covering (1, r) and (2, r)
        -- But (2, r) is already covered by d - contradiction with pairwise disjoint!
        have h2 : d.cell2 ∈ Rectangle 2 3 :=
          h_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [mem_Rectangle] at h2
        -- d.cell1 = (2, r) for some r ∈ {1, 2, 3}
        have hr_bounds : d.cell1.2 ≥ 1 ∧ d.cell1.2 ≤ 3 := ⟨h1.2.2.1, h1.2.2.2⟩
        -- Cell (1, d.cell1.2) is in the rectangle and must be covered
        have h_cell_in_rect : (1, d.cell1.2) ∈ Rectangle 2 3 := by
          rw [mem_Rectangle]; omega
        -- Find the domino d' that covers (1, d.cell1.2)
        have h_covered := T.covers_all
        rw [Finset.ext_iff] at h_covered
        have h_in_union : (1, d.cell1.2) ∈ T.dominos.biUnion Domino.cells := by
          rw [h_covered]; exact h_cell_in_rect
        rw [Finset.mem_biUnion] at h_in_union
        obtain ⟨d', hd'_mem, hd'_covers⟩ := h_in_union
        -- d' covers (1, d.cell1.2), so d'.cell1 = (1, r) or d'.cell2 = (1, r) where r = d.cell1.2
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_covers
        -- d' is either vertical or horizontal
        rcases d'.adjacent with ⟨hcol', _⟩ | ⟨hrow', hcol_adj'⟩
        · -- d' is vertical
          -- d'.cell1.1 = d'.cell2.1
          -- Since d' covers (1, r), we have d'.cell1.1 = 1 or d'.cell2.1 = 1
          -- So d' is vertical in column 1 - contradiction!
          rcases hd'_covers with hc1 | hc2
          · -- d'.cell1 = (1, d.cell1.2)
            have : d'.cell1.1 = 1 := by rw [← hc1]
            apply hno_vert
            exact ⟨d', hd'_mem, hcol', this⟩
          · -- d'.cell2 = (1, d.cell1.2)
            have hc2_col : d'.cell2.1 = 1 := by rw [← hc2]
            have hc1_col : d'.cell1.1 = 1 := hcol'.symm ▸ hc2_col
            apply hno_vert
            exact ⟨d', hd'_mem, hcol', hc1_col⟩
        · -- d' is horizontal: d'.cell1.2 = d'.cell2.2
          -- d' covers (1, r) and extends horizontally
          -- From adjacency, d'.cell1.1 + 1 = d'.cell2.1 or d'.cell2.1 + 1 = d'.cell1.1
          -- Combined with d' covering (1, r), d' must cover (1, r) and (2, r)
          -- But (2, r) = (2, d.cell1.2) is covered by d (since d.cell1 = (2, d.cell1.2))
          -- This contradicts pairwise disjoint!
          rcases hd'_covers with hc1 | hc2
          · -- d'.cell1 = (1, d.cell1.2)
            -- d'.cell2.2 = d'.cell1.2 = d.cell1.2
            have hd'1_row : d'.cell1.2 = d.cell1.2 := (congrArg Prod.snd hc1).symm
            have hd'_row : d'.cell2.2 = d.cell1.2 := hrow'.symm.trans hd'1_row
            -- d'.cell2.1 = 2 (from adjacency and bounds)
            have hd'_in_rect := T.dominos_in_rect d' hd'_mem
            have hd'2_in : d'.cell2 ∈ Rectangle 2 3 :=
              hd'_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            rw [mem_Rectangle] at hd'2_in
            have hd'1_col : d'.cell1.1 = 1 := (congrArg Prod.fst hc1).symm
            rcases hcol_adj' with hadj | hadj
            · -- d'.cell1.1 + 1 = d'.cell2.1
              have hd'2_col : d'.cell2.1 = 2 := by omega
              -- d'.cell2 = (2, d.cell1.2)
              have hd'2_eq : d'.cell2 = (2, d.cell1.2) := Prod.ext hd'2_col hd'_row
              -- d.cell1 = (2, d.cell1.2) (since d.cell1.1 = 2 from hc)
              have hd1_eq : d.cell1 = (2, d.cell1.2) := Prod.ext hc rfl
              -- d'.cell2 = d.cell1
              have h_overlap : d'.cell2 = d.cell1 := by rw [hd'2_eq, hd1_eq]
              -- d' ≠ d (d' covers column 1, d is in column 2)
              have hne : d' ≠ d := by
                intro heq; subst heq
                omega
              -- d' and d share cell d.cell1, contradicting pairwise disjoint
              have h_disj := T.pairwise_disjoint d' hd'_mem d hd hne
              rw [Finset.disjoint_iff_ne] at h_disj
              have h_d1_in_d' : d.cell1 ∈ d'.cells := by
                simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
                right; exact h_overlap.symm
              have h_d1_in_d : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
              exact h_disj d.cell1 h_d1_in_d' d.cell1 h_d1_in_d rfl
            · -- d'.cell2.1 + 1 = d'.cell1.1
              -- d'.cell1.1 = 1 (from hc1), so d'.cell2.1 = 0
              -- But d'.cell2 ∈ Rectangle 2 3, so d'.cell2.1 ≥ 1 - contradiction!
              omega
          · -- d'.cell2 = (1, d.cell1.2)
            -- Similar argument
            have hd'2_row : d'.cell2.2 = d.cell1.2 := (congrArg Prod.snd hc2).symm
            have hd'_row : d'.cell1.2 = d.cell1.2 := hrow'.trans hd'2_row
            have hd'_in_rect := T.dominos_in_rect d' hd'_mem
            have hd'1_in : d'.cell1 ∈ Rectangle 2 3 :=
              hd'_in_rect (Finset.mem_insert_self _ _)
            rw [mem_Rectangle] at hd'1_in
            have hd'2_col : d'.cell2.1 = 1 := (congrArg Prod.fst hc2).symm
            rcases hcol_adj' with hadj | hadj
            · -- d'.cell1.1 + 1 = d'.cell2.1
              -- d'.cell2.1 = 1 (from hc2), so d'.cell1.1 = 0
              -- But d'.cell1 ∈ Rectangle 2 3, so d'.cell1.1 ≥ 1 - contradiction!
              omega
            · -- d'.cell2.1 + 1 = d'.cell1.1
              have hd'1_col : d'.cell1.1 = 2 := by omega
              have hd'1_eq : d'.cell1 = (2, d.cell1.2) := Prod.ext hd'1_col hd'_row
              have hd1_eq : d.cell1 = (2, d.cell1.2) := Prod.ext hc rfl
              have h_overlap : d'.cell1 = d.cell1 := by rw [hd'1_eq, hd1_eq]
              have hne : d' ≠ d := by
                intro heq; subst heq
                omega
              have h_disj := T.pairwise_disjoint d' hd'_mem d hd hne
              rw [Finset.disjoint_iff_ne] at h_disj
              have h_d1_in_d' : d.cell1 ∈ d'.cells := by
                simp only [Domino.cells, Finset.mem_insert]; left; exact h_overlap.symm
              have h_d1_in_d : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
              exact h_disj d.cell1 h_d1_in_d' d.cell1 h_d1_in_d rfl
    · -- Horizontal case
      exact hrow

  -- Now show the cells images are equal
  -- Each horizontal domino in T covers {(1, r), (2, r)} for some row r ∈ {1, 2, 3}
  -- Since T partitions Rectangle 2 3, exactly one domino covers each row
  -- So T.dominos.image Domino.cells = {{(1,1), (2,1)}, {(1,2), (2,2)}, {(1,3), (2,3)}}
  -- This equals TilingC.dominos.image Domino.cells
  -- The detailed proof follows from h_all_horiz and the structure of Rectangle 2 3

  -- Helper: each horizontal domino d in Rectangle 2 3 has d.cells = {(1, r), (2, r)} for some r
  have h_cells_form : ∀ d ∈ T.dominos, ∃ r : ℕ, r ≥ 1 ∧ r ≤ 3 ∧ d.cells = {(1, r), (2, r)} := by
    intro d hd
    have h_horiz := h_all_horiz d hd
    have h_in_rect := T.dominos_in_rect d hd
    unfold Domino.isHorizontal at h_horiz
    have h1 := h_in_rect (Finset.mem_insert_self _ _)
    have h2 := h_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [mem_Rectangle] at h1 h2
    use d.cell1.2
    refine ⟨h1.2.2.1, h1.2.2.2, ?_⟩
    unfold Domino.cells
    rcases d.adjacent with ⟨_, hadj⟩ | ⟨_, hadj⟩
    · omega  -- vertical case contradicts h_horiz
    · rcases hadj with hadj1 | hadj2
      · -- d.cell1.1 + 1 = d.cell2.1
        have hc1_col : d.cell1.1 = 1 := by omega
        have hc2_col : d.cell2.1 = 2 := by omega
        have hc1 : d.cell1 = (1, d.cell1.2) := Prod.ext hc1_col rfl
        have hc2 : d.cell2 = (2, d.cell1.2) := Prod.ext hc2_col h_horiz.symm
        rw [hc1, hc2]
      · -- d.cell2.1 + 1 = d.cell1.1
        have hc2_col : d.cell2.1 = 1 := by omega
        have hc1_col : d.cell1.1 = 2 := by omega
        have hc1 : d.cell1 = (2, d.cell1.2) := Prod.ext hc1_col rfl
        have hc2 : d.cell2 = (1, d.cell1.2) := Prod.ext hc2_col h_horiz.symm
        rw [hc1, hc2, Finset.pair_comm]

  -- TilingEquiv means the cell images are equal
  unfold DominoTiling.TilingEquiv
  -- TilingC.dominos.image Domino.cells = {{(1,1), (2,1)}, {(1,2), (2,2)}, {(1,3), (2,3)}}
  have hC_image : TilingC.dominos.image Domino.cells =
      {{(1, 1), (2, 1)}, {(1, 2), (2, 2)}, {(1, 3), (2, 3)}} := by
    unfold TilingC
    decide

  rw [hC_image]
  -- Now show T.dominos.image Domino.cells = {{(1,1), (2,1)}, {(1,2), (2,2)}, {(1,3), (2,3)}}
  ext x
  constructor
  · -- x ∈ T.dominos.image Domino.cells → x ∈ {{...}}
    intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd_mem, hd_eq⟩ := hx
    obtain ⟨r, hr_ge, hr_le, hr_cells⟩ := h_cells_form d hd_mem
    rw [← hd_eq, hr_cells]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases r <;> simp
  · -- x ∈ {{...}} → x ∈ T.dominos.image Domino.cells
    intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · -- x = {(1, 1), (2, 1)}
      -- Cell (1, 1) is covered by some domino d in T
      have h11_in : (1, 1) ∈ Rectangle 2 3 := by rw [mem_Rectangle]; omega
      have h11_covered : (1, 1) ∈ T.dominos.biUnion Domino.cells := by
        rw [T.covers_all]; exact h11_in
      rw [Finset.mem_biUnion] at h11_covered
      obtain ⟨d, hd_mem, hd_covers⟩ := h11_covered
      obtain ⟨r, _, _, hr_cells⟩ := h_cells_form d hd_mem
      rw [hr_cells] at hd_covers
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_covers
      rcases hd_covers with ⟨_, hr⟩ | ⟨_, hr⟩ <;> subst hr
      · rw [Finset.mem_image]; exact ⟨d, hd_mem, hr_cells⟩
      · rw [Finset.mem_image]; exact ⟨d, hd_mem, hr_cells⟩
    · -- x = {(1, 2), (2, 2)}
      have h12_in : (1, 2) ∈ Rectangle 2 3 := by rw [mem_Rectangle]; omega
      have h12_covered : (1, 2) ∈ T.dominos.biUnion Domino.cells := by
        rw [T.covers_all]; exact h12_in
      rw [Finset.mem_biUnion] at h12_covered
      obtain ⟨d, hd_mem, hd_covers⟩ := h12_covered
      obtain ⟨r, _, _, hr_cells⟩ := h_cells_form d hd_mem
      rw [hr_cells] at hd_covers
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_covers
      rcases hd_covers with ⟨_, hr⟩ | ⟨_, hr⟩ <;> subst hr
      · rw [Finset.mem_image]; exact ⟨d, hd_mem, hr_cells⟩
      · rw [Finset.mem_image]; exact ⟨d, hd_mem, hr_cells⟩
    · -- x = {(1, 3), (2, 3)}
      have h13_in : (1, 3) ∈ Rectangle 2 3 := by rw [mem_Rectangle]; omega
      have h13_covered : (1, 3) ∈ T.dominos.biUnion Domino.cells := by
        rw [T.covers_all]; exact h13_in
      rw [Finset.mem_biUnion] at h13_covered
      obtain ⟨d, hd_mem, hd_covers⟩ := h13_covered
      obtain ⟨r, _, _, hr_cells⟩ := h_cells_form d hd_mem
      rw [hr_cells] at hd_covers
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd_covers
      rcases hd_covers with ⟨_, hr⟩ | ⟨_, hr⟩ <;> subst hr
      · rw [Finset.mem_image]; exact ⟨d, hd_mem, hr_cells⟩
      · rw [Finset.mem_image]; exact ⟨d, hd_mem, hr_cells⟩

/-- (prop.gf.weighted-set.domino.Rn3.ABC (a))
    The faultfree domino tilings of a height-3 rectangle with a vertical domino in
    the top two squares of column 1 are precisely A_2, A_4, A_6, ...

    Proof sketch: By induction, the structure of the tiling is forced:
    - Claim 1 (`claim1_basement_middle_top`): The tiling must contain specific basement,
      middle, and top dominos
    - Claim 2 (`claim2_n_even`): n must be even (by parity or by showing odd n leads
      to contradiction)
    - The remaining squares can only be tiled one way, giving T ≃ A_n

    Note: We use TilingEquiv instead of = because the Domino structure distinguishes
    between {cell1 := (1, 2), cell2 := (1, 3)} and {cell1 := (1, 3), cell2 := (1, 2)}
    as different dominos, even though they cover the same cells. -/

lemma faultfree_top_vertical_classification (n : ℕ) (T : DominoTiling n 3)
    (hfree : T.isFaultfree) (htop : T.hasTopVerticalInCol 1) :
    Even n ∧ ∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingA n hn hn_ge) := by
  have hn_even := claim2_n_even n T hfree htop
  have hn_ge := faultfree_hasTopVerticalInCol_implies_n_ge_two n T hfree htop
  refine ⟨hn_even, hn_even, hn_ge, ?_⟩
  -- The uniqueness proof: TilingEquiv T (TilingA n hn_even hn_ge)
  -- TilingEquiv means T.dominos.image Domino.cells = TilingA.dominos.image Domino.cells
  -- This is easier than showing T.dominos = TilingA.dominos because we don't need
  -- exact cell ordering within each domino.
  unfold DominoTiling.TilingEquiv
  -- Both tilings cover the same rectangle, so they have the same number of dominos
  have h_card_T := T.card_eq_twice_dominos
  have h_card_A := (TilingA n hn_even hn_ge).card_eq_twice_dominos
  simp only [card_Rectangle] at h_card_T h_card_A
  have h_card_eq : T.dominos.card = (TilingA n hn_even hn_ge).dominos.card := by omega
  -- Both tilings cover the same cells (the rectangle), so their cell images are equal
  -- We show this by showing each covers all cells of the rectangle
  have hT_cells : T.dominos.biUnion Domino.cells = Rectangle n 3 := T.covers_all
  have hA_cells : (TilingA n hn_even hn_ge).dominos.biUnion Domino.cells = Rectangle n 3 :=
    (TilingA n hn_even hn_ge).covers_all
  -- The image of cells is the set of all cell-pairs covered
  -- Since both tilings partition the same rectangle, their cell images are determined
  -- by which cells are covered together (as dominos)
  -- For a tiling, each cell appears in exactly one domino, so the image is a partition
  -- Two partitions of the same set with the same number of parts must have parts of
  -- the same sizes (all size 2 for dominos), but not necessarily the same parts
  -- However, we can show the parts are the same by using the structure of the tilings
  -- Strategy: We show both sets are equal by showing one is a subset of the other
  -- and they have the same cardinality.
  -- Key insight: in a tiling, Domino.cells is injective because different dominos have disjoint cells
  have h_cells_inj_T : ∀ d₁ ∈ T.dominos, ∀ d₂ ∈ T.dominos, d₁.cells = d₂.cells → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ h_eq
    by_contra hne
    have h_disj := T.pairwise_disjoint d₁ hd₁ d₂ hd₂ hne
    rw [Finset.disjoint_iff_ne] at h_disj
    have h_cell1 : d₁.cell1 ∈ d₁.cells := by simp [Domino.cells]
    have h_cell1' : d₁.cell1 ∈ d₂.cells := by rw [← h_eq]; exact h_cell1
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cell1'
    rcases h_cell1' with h | h
    · have h_mem : d₁.cell1 ∈ d₂.cells := by simp [Domino.cells, h]
      exact h_disj d₁.cell1 h_cell1 d₁.cell1 h_mem rfl
    · have h_mem : d₁.cell1 ∈ d₂.cells := by simp [Domino.cells, h]
      exact h_disj d₁.cell1 h_cell1 d₁.cell1 h_mem rfl
  have h_cells_inj_A : ∀ d₁ ∈ (TilingA n hn_even hn_ge).dominos,
      ∀ d₂ ∈ (TilingA n hn_even hn_ge).dominos, d₁.cells = d₂.cells → d₁ = d₂ := by
    intro d₁ hd₁ d₂ hd₂ h_eq
    by_contra hne
    have h_disj := (TilingA n hn_even hn_ge).pairwise_disjoint d₁ hd₁ d₂ hd₂ hne
    rw [Finset.disjoint_iff_ne] at h_disj
    have h_cell1 : d₁.cell1 ∈ d₁.cells := by simp [Domino.cells]
    have h_cell1' : d₁.cell1 ∈ d₂.cells := by rw [← h_eq]; exact h_cell1
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cell1'
    rcases h_cell1' with h | h
    · have h_mem : d₁.cell1 ∈ d₂.cells := by simp [Domino.cells, h]
      exact h_disj d₁.cell1 h_cell1 d₁.cell1 h_mem rfl
    · have h_mem : d₁.cell1 ∈ d₂.cells := by simp [Domino.cells, h]
      exact h_disj d₁.cell1 h_cell1 d₁.cell1 h_mem rfl
  -- Prove the backward direction: TilingA.dominos.image Domino.cells ⊆ T.dominos.image Domino.cells
  have h_backward : (TilingA n hn_even hn_ge).dominos.image Domino.cells ⊆ T.dominos.image Domino.cells := by
    intro S hS
    rw [Finset.mem_image] at hS ⊢
    obtain ⟨d, hd_mem, hd_cells⟩ := hS
    -- d is a domino in TilingA, we need to find a domino in T with the same cells
    change d ∈ basementDominos n ∪ {leftWall} ∪ {rightWall n} ∪ middleDominos n ∪ topDominos n at hd_mem
    simp only [Finset.mem_union, Finset.mem_singleton] at hd_mem
    rcases hd_mem with ((((hd | hd) | hd) | hd) | hd)
    · -- d ∈ basementDominos n
      simp only [basementDominos, Finset.mem_map, Finset.mem_range] at hd
      obtain ⟨j, hj_lt, hd_eq⟩ := hd
      have hd_cell1 : d.cell1 = (2 * j + 1, 1) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hd_cell2 : d.cell2 = (2 * j + 2, 1) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      by_cases hj : j < n / 2 - 1
      · -- j < n/2 - 1: use claim1 with i = j + 1
        have hi_pos : j + 1 ≥ 1 := by omega
        have hi_lt : j + 1 < n / 2 := by omega
        obtain ⟨⟨d', hd'_mem, hd'_cells⟩, _, _⟩ :=
          claim1_basement_middle_top n T hfree htop (j + 1) hi_pos hi_lt
        use d', hd'_mem
        rw [← hd_cells]
        simp only [Domino.cells, hd_cell1, hd_cell2]
        change d'.cells = {(2 * j + 1, 1), (2 * j + 2, 1)}
        rw [hd'_cells]
        have h1 : (2 * (j + 1) - 1, 1) = (2 * j + 1, 1) := by ext <;> omega
        have h2 : (2 * (j + 1), 1) = (2 * j + 2, 1) := by ext <;> omega
        simp [h1, h2]
      · -- j = n/2 - 1: last basement domino (n-1, 1) - (n, 1)
        have hj_eq : j = n / 2 - 1 := by omega
        have hd_c1 : d.cell1 = (n - 1, 1) := by
          rw [hd_cell1, hj_eq]
          obtain ⟨k, hk⟩ := hn_even; subst hk
          have hkk : (k + k) / 2 = k := by omega
          simp only [hkk]; ext <;> omega
        have hd_c2 : d.cell2 = (n, 1) := by
          rw [hd_cell2, hj_eq]
          obtain ⟨k, hk⟩ := hn_even; subst hk
          have hkk : (k + k) / 2 = k := by omega
          simp only [hkk]; ext <;> omega
        have hn3_in_rect : (n, 3) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
        obtain ⟨d_n3, hd_n3_mem, hd_n3_cov⟩ := T.cell_covered (n, 3) hn3_in_rect
        have hd_n3_in_rect := T.dominos_in_rect d_n3 hd_n3_mem
        have h_n3_opts := domino_at_n3_options n d_n3 hd_n3_in_rect hd_n3_cov
        have hd_n3_cells : d_n3.cells = {(n, 2), (n, 3)} := by
          rcases h_n3_opts with h_left | h_right
          · exfalso
            rcases Nat.lt_or_ge n 4 with hn_lt4 | hn_ge4
            · have hn2 : n = 2 := by obtain ⟨k, hk⟩ := hn_even; omega
              obtain ⟨d_lw, hd_lw_mem, hd_lw_vert, hd_lw_col, hd_lw_rows⟩ := htop
              have hd_lw_c2_col : d_lw.cell2.1 = 1 := by rw [← hd_lw_vert, hd_lw_col]
              have h_13_in_lw : (1, 3) ∈ d_lw.cells := by
                simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
                rcases hd_lw_rows with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · right; exact Prod.ext hd_lw_c2_col.symm h2.symm
                · left; exact Prod.ext hd_lw_col.symm h1.symm
              have h_n1_3 : (n - 1, 3) = (1, 3) := by simp [hn2]
              have h_13_in_n3 : (1, 3) ∈ d_n3.cells := by rw [h_left, h_n1_3]; simp
              by_cases heq : d_lw = d_n3
              · have hd_lw_cells : d_lw.cells = {(1, 2), (1, 3)} := by
                  simp only [Domino.cells]
                  rcases hd_lw_rows with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · have hc1 : d_lw.cell1 = (1, 2) := Prod.ext hd_lw_col h1
                    have hc2 : d_lw.cell2 = (1, 3) := Prod.ext hd_lw_c2_col h2
                    simp [hc1, hc2]
                  · have hc1 : d_lw.cell1 = (1, 3) := Prod.ext hd_lw_col h1
                    have hc2 : d_lw.cell2 = (1, 2) := Prod.ext hd_lw_c2_col h2
                    simp [hc1, hc2, Finset.pair_comm]
                rw [heq, h_left, h_n1_3] at hd_lw_cells
                simp only [hn2] at hd_lw_cells
                have : (2, 3) ∈ ({(1, 3), (2, 3)} : Finset Cell) := by simp
                rw [hd_lw_cells] at this; simp at this
              · have h_disj := T.pairwise_disjoint d_lw hd_lw_mem d_n3 hd_n3_mem heq
                rw [Finset.disjoint_iff_ne] at h_disj
                exact h_disj (1, 3) h_13_in_lw (1, 3) h_13_in_n3 rfl
            · have hi_pos : n / 2 - 2 + 1 ≥ 1 := by omega
              have hi_lt : n / 2 - 2 + 1 < n / 2 := by omega
              obtain ⟨_, _, ⟨d_top, hd_top_mem, hd_top_cells⟩⟩ :=
                claim1_basement_middle_top n T hfree htop (n / 2 - 2 + 1) hi_pos hi_lt
              have h_top_c1 : 2 * (n / 2 - 2 + 1) = n - 2 := by obtain ⟨k, hk⟩ := hn_even; omega
              have h_top_c2 : 2 * (n / 2 - 2 + 1) + 1 = n - 1 := by obtain ⟨k, hk⟩ := hn_even; omega
              have hd_top_cells' : d_top.cells = {(n - 2, 3), (n - 1, 3)} := by
                rw [hd_top_cells, h_top_c2, h_top_c1]
              have h_n1_3_in_top : (n - 1, 3) ∈ d_top.cells := by rw [hd_top_cells']; simp
              have h_n1_3_in_n3 : (n - 1, 3) ∈ d_n3.cells := by rw [h_left]; simp
              by_cases heq : d_top = d_n3
              · rw [heq, h_left] at hd_top_cells'
                have h_n2 : (n - 2, 3) ∈ ({(n - 1, 3), (n, 3)} : Finset Cell) := by
                  rw [hd_top_cells']; simp
                simp only [Finset.mem_insert, Finset.mem_singleton] at h_n2
                rcases h_n2 with h1 | h2
                · simp only [Prod.mk.injEq] at h1; obtain ⟨h1a, _⟩ := h1; omega
                · simp only [Prod.mk.injEq] at h2; obtain ⟨h2a, _⟩ := h2; omega
              · have h_disj := T.pairwise_disjoint d_top hd_top_mem d_n3 hd_n3_mem heq
                rw [Finset.disjoint_iff_ne] at h_disj
                exact h_disj (n - 1, 3) h_n1_3_in_top (n - 1, 3) h_n1_3_in_n3 rfl
          · exact h_right
        have h_n2_in_n3 : (n, 2) ∈ d_n3.cells := by rw [hd_n3_cells]; simp
        have hn1_in_rect : (n, 1) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
        obtain ⟨d_n1, hd_n1_mem, hd_n1_cov⟩ := T.cell_covered (n, 1) hn1_in_rect
        have hd_n1_in_rect := T.dominos_in_rect d_n1 hd_n1_mem
        have h_n1_opts := domino_at_n1_options n d_n1 hd_n1_in_rect hd_n1_cov
        have hd_n1_cells : d_n1.cells = {(n - 1, 1), (n, 1)} := by
          rcases h_n1_opts with h_left | h_right
          · exact h_left
          · exfalso
            have h_n2_in_n1 : (n, 2) ∈ d_n1.cells := by rw [h_right]; simp
            by_cases heq : d_n1 = d_n3
            · rw [heq, hd_n3_cells] at h_right
              have h_n1 : (n, 1) ∈ ({(n, 2), (n, 3)} : Finset Cell) := by rw [h_right]; simp
              simp at h_n1
            · have h_disj := T.pairwise_disjoint d_n1 hd_n1_mem d_n3 hd_n3_mem heq
              rw [Finset.disjoint_iff_ne] at h_disj
              exact h_disj (n, 2) h_n2_in_n1 (n, 2) h_n2_in_n3 rfl
        use d_n1, hd_n1_mem
        rw [← hd_cells]
        simp only [Domino.cells, hd_c1, hd_c2]
        rw [show ({d_n1.cell1, d_n1.cell2} : Finset Cell) = d_n1.cells from rfl, hd_n1_cells]
    · -- d = leftWall
      obtain ⟨d', hd'_mem, hd'_vert, hd'_col, hd'_rows⟩ := htop
      use d', hd'_mem
      rw [← hd_cells]
      simp only [Domino.cells, leftWall] at hd ⊢
      have hcol2 : d'.cell2.1 = 1 := by rw [← hd'_vert, hd'_col]
      rcases hd'_rows with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hc1 : d'.cell1 = (1, 2) := Prod.ext hd'_col h1
        have hc2 : d'.cell2 = (1, 3) := Prod.ext hcol2 h2
        simp only [hd, hc1, hc2]
      · have hc1 : d'.cell1 = (1, 3) := Prod.ext hd'_col h1
        have hc2 : d'.cell2 = (1, 2) := Prod.ext hcol2 h2
        simp only [hd, hc1, hc2, Finset.pair_comm]
    · -- d = rightWall n
      simp only [rightWall] at hd
      have hd_c1 : d.cell1 = (n, 2) := by simp [hd]
      have hd_c2 : d.cell2 = (n, 3) := by simp [hd]
      have hn3_in_rect : (n, 3) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
      obtain ⟨d_n3, hd_n3_mem, hd_n3_cov⟩ := T.cell_covered (n, 3) hn3_in_rect
      have hd_n3_in_rect := T.dominos_in_rect d_n3 hd_n3_mem
      have h_n3_opts := domino_at_n3_options n d_n3 hd_n3_in_rect hd_n3_cov
      have hd_n3_cells : d_n3.cells = {(n, 2), (n, 3)} := by
        rcases h_n3_opts with h_left | h_right
        · exfalso
          rcases Nat.lt_or_ge n 4 with hn_lt4 | hn_ge4
          · have hn2 : n = 2 := by obtain ⟨k, hk⟩ := hn_even; omega
            obtain ⟨d_lw, hd_lw_mem, hd_lw_vert, hd_lw_col, hd_lw_rows⟩ := htop
            have hd_lw_c2_col : d_lw.cell2.1 = 1 := by rw [← hd_lw_vert, hd_lw_col]
            have h_13_in_lw : (1, 3) ∈ d_lw.cells := by
              simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              rcases hd_lw_rows with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · right; exact Prod.ext hd_lw_c2_col.symm h2.symm
              · left; exact Prod.ext hd_lw_col.symm h1.symm
            have h_n1_3 : (n - 1, 3) = (1, 3) := by simp [hn2]
            have h_13_in_n3 : (1, 3) ∈ d_n3.cells := by rw [h_left, h_n1_3]; simp
            by_cases heq : d_lw = d_n3
            · have hd_lw_cells : d_lw.cells = {(1, 2), (1, 3)} := by
                simp only [Domino.cells]
                rcases hd_lw_rows with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · have hc1 : d_lw.cell1 = (1, 2) := Prod.ext hd_lw_col h1
                  have hc2 : d_lw.cell2 = (1, 3) := Prod.ext hd_lw_c2_col h2
                  simp [hc1, hc2]
                · have hc1 : d_lw.cell1 = (1, 3) := Prod.ext hd_lw_col h1
                  have hc2 : d_lw.cell2 = (1, 2) := Prod.ext hd_lw_c2_col h2
                  simp [hc1, hc2, Finset.pair_comm]
              rw [heq, h_left, h_n1_3] at hd_lw_cells
              simp only [hn2] at hd_lw_cells
              have : (2, 3) ∈ ({(1, 3), (2, 3)} : Finset Cell) := by simp
              rw [hd_lw_cells] at this; simp at this
            · have h_disj := T.pairwise_disjoint d_lw hd_lw_mem d_n3 hd_n3_mem heq
              rw [Finset.disjoint_iff_ne] at h_disj
              exact h_disj (1, 3) h_13_in_lw (1, 3) h_13_in_n3 rfl
          · have hi_pos : n / 2 - 2 + 1 ≥ 1 := by omega
            have hi_lt : n / 2 - 2 + 1 < n / 2 := by omega
            obtain ⟨_, _, ⟨d_top, hd_top_mem, hd_top_cells⟩⟩ :=
              claim1_basement_middle_top n T hfree htop (n / 2 - 2 + 1) hi_pos hi_lt
            have h_top_c1 : 2 * (n / 2 - 2 + 1) = n - 2 := by obtain ⟨k, hk⟩ := hn_even; omega
            have h_top_c2 : 2 * (n / 2 - 2 + 1) + 1 = n - 1 := by obtain ⟨k, hk⟩ := hn_even; omega
            have hd_top_cells' : d_top.cells = {(n - 2, 3), (n - 1, 3)} := by
              rw [hd_top_cells, h_top_c2, h_top_c1]
            have h_n1_3_in_top : (n - 1, 3) ∈ d_top.cells := by rw [hd_top_cells']; simp
            have h_n1_3_in_n3 : (n - 1, 3) ∈ d_n3.cells := by rw [h_left]; simp
            by_cases heq : d_top = d_n3
            · rw [heq, h_left] at hd_top_cells'
              have h_n2 : (n - 2, 3) ∈ ({(n - 1, 3), (n, 3)} : Finset Cell) := by
                rw [hd_top_cells']; simp
              simp only [Finset.mem_insert, Finset.mem_singleton] at h_n2
              rcases h_n2 with h1 | h2
              · simp only [Prod.mk.injEq] at h1; obtain ⟨h1a, _⟩ := h1; omega
              · simp only [Prod.mk.injEq] at h2; obtain ⟨h2a, _⟩ := h2; omega
            · have h_disj := T.pairwise_disjoint d_top hd_top_mem d_n3 hd_n3_mem heq
              rw [Finset.disjoint_iff_ne] at h_disj
              exact h_disj (n - 1, 3) h_n1_3_in_top (n - 1, 3) h_n1_3_in_n3 rfl
        · exact h_right
      use d_n3, hd_n3_mem
      rw [← hd_cells]
      simp only [Domino.cells, hd_c1, hd_c2]
      rw [show ({d_n3.cell1, d_n3.cell2} : Finset Cell) = d_n3.cells from rfl, hd_n3_cells]
    · -- d ∈ middleDominos n
      simp only [middleDominos, Finset.mem_map, Finset.mem_range] at hd
      obtain ⟨j, hj_lt, hd_eq⟩ := hd
      have hd_cell1 : d.cell1 = (2 * j + 2, 2) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hd_cell2 : d.cell2 = (2 * j + 3, 2) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hi_pos : j + 1 ≥ 1 := by omega
      have hi_lt : j + 1 < n / 2 := by omega
      obtain ⟨_, ⟨d', hd'_mem, hd'_cells⟩, _⟩ :=
        claim1_basement_middle_top n T hfree htop (j + 1) hi_pos hi_lt
      use d', hd'_mem
      rw [← hd_cells]
      simp only [Domino.cells, hd_cell1, hd_cell2]
      change d'.cells = {(2 * j + 2, 2), (2 * j + 3, 2)}
      rw [hd'_cells]
      have h1 : (2 * (j + 1), 2) = (2 * j + 2, 2) := by ext <;> omega
      have h2 : (2 * (j + 1) + 1, 2) = (2 * j + 3, 2) := by ext <;> omega
      simp [h1, h2]
    · -- d ∈ topDominos n
      simp only [topDominos, Finset.mem_map, Finset.mem_range] at hd
      obtain ⟨j, hj_lt, hd_eq⟩ := hd
      have hd_cell1 : d.cell1 = (2 * j + 2, 3) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hd_cell2 : d.cell2 = (2 * j + 3, 3) := by
        simp only [← Function.Embedding.toFun_eq_coe] at hd_eq; rw [← hd_eq]
      have hi_pos : j + 1 ≥ 1 := by omega
      have hi_lt : j + 1 < n / 2 := by omega
      obtain ⟨_, _, ⟨d', hd'_mem, hd'_cells⟩⟩ :=
        claim1_basement_middle_top n T hfree htop (j + 1) hi_pos hi_lt
      use d', hd'_mem
      rw [← hd_cells]
      simp only [Domino.cells, hd_cell1, hd_cell2]
      change d'.cells = {(2 * j + 2, 3), (2 * j + 3, 3)}
      rw [hd'_cells]
      have h1 : (2 * (j + 1), 3) = (2 * j + 2, 3) := by ext <;> omega
      have h2 : (2 * (j + 1) + 1, 3) = (2 * j + 3, 3) := by ext <;> omega
      simp [h1, h2]
  -- Now use cardinality to show equality
  have h_image_card_eq : (T.dominos.image Domino.cells).card =
      ((TilingA n hn_even hn_ge).dominos.image Domino.cells).card := by
    have h1 : (T.dominos.image Domino.cells).card = T.dominos.card := by
      rw [Finset.card_image_of_injOn]
      exact h_cells_inj_T
    have h2 : ((TilingA n hn_even hn_ge).dominos.image Domino.cells).card =
        (TilingA n hn_even hn_ge).dominos.card := by
      rw [Finset.card_image_of_injOn]
      exact h_cells_inj_A
    omega
  -- By subset and equal cardinality, the sets are equal
  exact (Finset.eq_of_subset_of_card_le h_backward (by omega)).symm

/-- (prop.gf.weighted-set.domino.Rn3.ABC (b))
    The faultfree domino tilings of a height-3 rectangle with a vertical domino in
    the bottom two squares of column 1 are precisely B_2, B_4, B_6, ...

    This follows from part (a) by reflection across the horizontal axis.

    Note: We use TilingEquiv instead of = because the Domino structure distinguishes
    between different cell orderings. -/

lemma faultfree_bottom_vertical_classification (n : ℕ) (T : DominoTiling n 3)
    (hfree : T.isFaultfree) (hbot : T.hasBottomVerticalInCol 1) :
    Even n ∧ ∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingB n hn hn_ge) := by
  -- Reflect T to get T' with top vertical
  let T' := reflectTiling3 T
  -- T' is faultfree
  have hfree' : T'.isFaultfree := reflectTiling3_isFaultfree T hfree
  -- T' has top vertical in column 1
  have htop' : T'.hasTopVerticalInCol 1 := by
    rw [reflectTiling3_hasTopVertical_iff_hasBottomVertical]
    exact hbot
  -- Apply classification to T'
  obtain ⟨hn, hn_even, hn_ge, hT'⟩ := faultfree_top_vertical_classification n T' hfree' htop'
  constructor
  · exact hn
  · use hn_even, hn_ge
    -- T' ≃ TilingA n, so T ≃ reflectTiling3 T' ≃ reflectTiling3 (TilingA n) = TilingB n
    -- TilingEquiv is defined as equality of cell images
    -- reflectTiling3 preserves TilingEquiv because it's a bijection on cells
    unfold DominoTiling.TilingEquiv at hT' ⊢
    -- hT' : T'.dominos.image Domino.cells = (TilingA n hn_even hn_ge).dominos.image Domino.cells
    -- Goal: T.dominos.image Domino.cells = (TilingB n hn_even hn_ge).dominos.image Domino.cells
    -- T = reflectTiling3 (reflectTiling3 T) = reflectTiling3 T'
    have hT_eq : T = reflectTiling3 T' := (reflectTiling3_involutive T).symm
    -- TilingB n = reflectTiling3 (TilingA n)
    have hB_eq : TilingB n hn_even hn_ge = reflectTiling3 (TilingA n hn_even hn_ge) :=
      TilingB_eq_reflectTiling3_TilingA n hn_even hn_ge
    rw [hT_eq, hB_eq]
    -- Now show: (reflectTiling3 T').dominos.image Domino.cells =
    --           (reflectTiling3 (TilingA n)).dominos.image Domino.cells
    -- This follows because reflectTiling3 preserves TilingEquiv
    exact reflectTiling3_preserves_TilingEquiv T' (TilingA n hn_even hn_ge) hT'

/-- For height 3, a vertical domino in column 1 must be either in the top two squares
    (rows 2-3) or the bottom two squares (rows 1-2). There's no other option since
    a vertical domino covers 2 adjacent rows and we only have 3 rows. -/

lemma vertical_in_col1_trichotomy (n : ℕ) (T : DominoTiling n 3) :
    T.hasVerticalInCol 1 → T.hasTopVerticalInCol 1 ∨ T.hasBottomVerticalInCol 1 := by
  intro ⟨d, hd_mem, hd_vert, hd_col⟩
  -- d is a vertical domino in column 1
  -- Both cells of d are in the rectangle R_{n,3}
  have hd_in_rect := T.dominos_in_rect d hd_mem
  have hcell1 : d.cell1 ∈ Rectangle n 3 := hd_in_rect (Finset.mem_insert_self _ _)
  have hcell2 : d.cell2 ∈ Rectangle n 3 :=
    hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- Get row bounds from rectangle membership
  simp only [Rectangle, Finset.mem_map, ← Function.Embedding.toFun_eq_coe, Finset.mem_product,
    Finset.mem_range, Prod.exists] at hcell1 hcell2
  obtain ⟨x1, y1, ⟨_, hy1⟩, heq1⟩ := hcell1
  obtain ⟨x2, y2, ⟨_, hy2⟩, heq2⟩ := hcell2
  -- From heq1, heq2: d.cell1 = (x1+1, y1+1), d.cell2 = (x2+1, y2+1)
  -- So row bounds: 1 ≤ d.cell1.2 = y1+1 ≤ 3, 1 ≤ d.cell2.2 = y2+1 ≤ 3
  have h1_row_ge : 1 ≤ d.cell1.2 := by rw [← heq1]; omega
  have h1_row_le : d.cell1.2 ≤ 3 := by rw [← heq1]; omega
  have h2_row_ge : 1 ≤ d.cell2.2 := by rw [← heq2]; omega
  have h2_row_le : d.cell2.2 ≤ 3 := by rw [← heq2]; omega
  -- Since d is vertical, from adjacent property we have row relationship
  have hadj := d.adjacent
  rcases hadj with ⟨_, hrow_rel⟩ | ⟨_, hcol_rel⟩
  · -- Vertical case: same column, adjacent rows
    rcases hrow_rel with h1 | h2
    · -- cell1.2 + 1 = cell2.2: rows are (r, r+1) for some r
      -- With bounds 1 ≤ row ≤ 3, we have r ∈ {1, 2}
      have : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
      rcases this with h | h
      · -- rows 1 and 2: bottom vertical
        right
        exact ⟨d, hd_mem, hd_vert, hd_col, Or.inl ⟨h, by omega⟩⟩
      · -- rows 2 and 3: top vertical
        left
        exact ⟨d, hd_mem, hd_vert, hd_col, Or.inl ⟨by omega, by omega⟩⟩
    · -- cell2.2 + 1 = cell1.2
      have : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
      rcases this with h | h
      · -- rows 2 and 1: bottom vertical
        right
        exact ⟨d, hd_mem, hd_vert, hd_col, Or.inr ⟨by omega, h⟩⟩
      · -- rows 3 and 2: top vertical
        left
        exact ⟨d, hd_mem, hd_vert, hd_col, Or.inr ⟨by omega, by omega⟩⟩
  · -- Horizontal case: same row, adjacent columns
    -- But d is vertical, so cell1.1 = cell2.1
    -- This contradicts being horizontal (adjacent columns)
    exfalso
    unfold Domino.isVertical at hd_vert
    rcases hcol_rel with h | h <;> omega

/-- If a faultfree tiling has no vertical domino in column 1, then n = 2.

    Proof sketch: If the first column has no vertical domino, it must be filled with
    three horizontal dominos extending into column 2. This covers all of column 2,
    so if n > 2, there would be a fault between columns 2 and 3.

    Note: requires n ≥ 1 (for n = 0, the empty tiling is a counterexample). -/

lemma no_vertical_implies_n_eq_2 (n : ℕ) (T : DominoTiling n 3)
    (hfree : T.isFaultfree) (hno_vert : ¬T.hasVerticalInCol 1) (hn : n ≥ 1) :
    n = 2 := by
  -- Handle edge cases n = 1 and n = 2
  rcases Nat.lt_trichotomy n 2 with hn_lt | hn_eq | hn_gt
  · -- n < 2, so n = 1 (since n ≥ 1)
    have hn1 : n = 1 := by omega
    -- n = 1: No valid tiling exists (3 cells can't be covered by dominos)
    exfalso
    have h := T.card_eq_twice_dominos
    simp only [card_Rectangle, hn1] at h
    omega
  · exact hn_eq  -- n = 2
  · -- n > 2: derive contradiction by showing there's a fault at column 2
    exfalso
    have hn_ge_3 : n ≥ 3 := hn_gt
    -- The key insight: all dominos covering column 1 must be horizontal (no vertical allowed)
    -- and span columns 1-2. This means all cells in column 2 are covered by these dominos.
    -- Any domino with minCol = 2 would overlap with a column-1 domino, contradiction.
    -- So no domino spans columns 2-3, creating a fault at column 2.
    have hfault : T.hasFaultAt 2 := by
      refine ⟨by omega, hn_ge_3, ?_⟩
      intro d hd
      push Not
      intro hmin
      -- hmin : d.minCol ≤ 2, goal: d.maxCol ≤ 2
      have hd_in_rect := T.dominos_in_rect d hd
      have hc1_in_rect : d.cell1 ∈ Rectangle n 3 := hd_in_rect (by simp [Domino.cells])
      have hc2_in_rect : d.cell2 ∈ Rectangle n 3 := hd_in_rect (by simp [Domino.cells])
      rw [mem_Rectangle] at hc1_in_rect hc2_in_rect
      have hcol1_ge : d.cell1.1 ≥ 1 := hc1_in_rect.1
      have hcol2_ge : d.cell2.1 ≥ 1 := hc2_in_rect.1
      -- Case split on whether d touches column 1
      by_cases hmin1 : d.minCol = 1
      · -- d touches column 1: it must be horizontal spanning 1-2
        -- First, find which cell is in column 1
        have hcov1 : ∃ y, (1, y) ∈ d.cells := by
          unfold Domino.minCol at hmin1
          by_cases h : d.cell1.1 ≤ d.cell2.1
          · simp only [min_eq_left h] at hmin1
            exact ⟨d.cell1.2, by simp [Domino.cells]; left; rw [← hmin1]⟩
          · push Not at h
            simp only [min_eq_right (le_of_lt h)] at hmin1
            exact ⟨d.cell2.2, by simp [Domino.cells]; right; rw [← hmin1]⟩
        -- d is not vertical (since no vertical in column 1)
        have hd_novert : ¬d.isVertical := by
          intro hvert
          apply hno_vert
          unfold DominoTiling.hasVerticalInCol
          obtain ⟨y, hy⟩ := hcov1
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with h | h
          · exact ⟨d, hd, hvert, by rw [← h]⟩
          · have hc2 : d.cell2.1 = 1 := by rw [← h]
            exact ⟨d, hd, hvert, by unfold Domino.isVertical at hvert; omega⟩
        -- d is horizontal with one cell in column 1, so it spans columns 1-2
        unfold Domino.isVertical at hd_novert
        rcases d.adjacent with ⟨hcol_eq, _⟩ | ⟨_, hcol_adj⟩
        · exact absurd hcol_eq hd_novert
        · -- d is horizontal, spanning columns 1-2
          unfold Domino.maxCol
          obtain ⟨y, hy⟩ := hcov1
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with h | h
          · have hc1 : d.cell1.1 = 1 := by rw [← h]
            rcases hcol_adj with hadj | hadj
            · simp only [hc1] at hadj; omega
            · simp only [hc1] at hadj; omega
          · have hc2 : d.cell2.1 = 1 := by rw [← h]
            rcases hcol_adj with hadj | hadj
            · simp only [hc2] at hadj; omega
            · simp only [hc2] at hadj; omega
      · -- d.minCol ≠ 1, so d.minCol = 2 (since d.minCol ≤ 2 and d.minCol ≥ 1)
        have hmin2 : d.minCol = 2 := by unfold Domino.minCol at hmin hmin1 ⊢; omega
        -- d has a cell in column 2
        unfold Domino.minCol at hmin2
        have hcell2 : d.cell1.1 = 2 ∨ d.cell2.1 = 2 := by
          by_cases h : d.cell1.1 ≤ d.cell2.1
          · left; simp only [min_eq_left h] at hmin2; exact hmin2
          · right; push Not at h; simp only [min_eq_right (le_of_lt h)] at hmin2; exact hmin2
        -- This cell in column 2 is covered by some domino d' that covers column 1
        -- d' must be horizontal spanning 1-2 (since no vertical in column 1)
        -- So d and d' both cover a cell in column 2, contradicting disjointness (unless d = d')
        -- But if d = d', then d.minCol = 1, contradicting hmin2
        rcases hcell2 with hc1_col | hc2_col
        · -- d.cell1 is in column 2
          -- The cell (1, d.cell1.2) is in the rectangle and covered by some domino d'
          have h1r : (1, d.cell1.2) ∈ Rectangle n 3 := by
            rw [mem_Rectangle]
            exact ⟨le_refl 1, by omega, hc1_in_rect.2.2.1, hc1_in_rect.2.2.2⟩
          -- Find the domino d' that covers (1, d.cell1.2)
          obtain ⟨d', hd'_mem, hd'_cov⟩ := T.cell_covered (1, d.cell1.2) h1r
          have hd'_min_le : d'.minCol ≤ 1 := by
            unfold Domino.minCol
            simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
            rcases hd'_cov with h | h
            · simp only [← h]; exact min_le_left _ _
            · simp only [← h]; exact min_le_right _ _
          have hd'_in_rect := T.dominos_in_rect d' hd'_mem
          have hd'_c1_in : d'.cell1 ∈ Rectangle n 3 := hd'_in_rect (by simp [Domino.cells])
          have hd'_c2_in : d'.cell2 ∈ Rectangle n 3 := hd'_in_rect (by simp [Domino.cells])
          rw [mem_Rectangle] at hd'_c1_in hd'_c2_in
          have hd'_col1_ge : d'.cell1.1 ≥ 1 := hd'_c1_in.1
          have hd'_col2_ge : d'.cell2.1 ≥ 1 := hd'_c2_in.1
          have hd'_min_eq : d'.minCol = 1 := by unfold Domino.minCol at hd'_min_le ⊢; omega
          have hd'_cov1 : ∃ y, (1, y) ∈ d'.cells := by
            unfold Domino.minCol at hd'_min_eq
            by_cases h : d'.cell1.1 ≤ d'.cell2.1
            · simp only [min_eq_left h] at hd'_min_eq
              exact ⟨d'.cell1.2, by simp [Domino.cells]; left; rw [← hd'_min_eq]⟩
            · push Not at h
              simp only [min_eq_right (le_of_lt h)] at hd'_min_eq
              exact ⟨d'.cell2.2, by simp [Domino.cells]; right; rw [← hd'_min_eq]⟩
          have hd'_novert : ¬d'.isVertical := by
            intro hvert
            apply hno_vert
            unfold DominoTiling.hasVerticalInCol
            obtain ⟨y, hy⟩ := hd'_cov1
            simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with h | h
            · exact ⟨d', hd'_mem, hvert, by rw [← h]⟩
            · have hc2' : d'.cell2.1 = 1 := by rw [← h]
              exact ⟨d', hd'_mem, hvert, by unfold Domino.isVertical at hvert; omega⟩
          unfold Domino.isVertical at hd'_novert
          rcases d'.adjacent with ⟨hcol_eq, _⟩ | ⟨hrow_eq, hcol_adj⟩
          · exact absurd hcol_eq hd'_novert
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
            rcases hd'_cov with hcov | hcov
            · have hd'c1 : d'.cell1 = (1, d.cell1.2) := hcov.symm
              have hd'c2_row : d'.cell2.2 = d.cell1.2 := by
                have h1 : d'.cell1.2 = d.cell1.2 := by rw [hd'c1]
                exact hrow_eq.symm.trans h1
              have hd'c2_col : d'.cell2.1 = 2 := by
                have h1 : d'.cell1.1 = 1 := by rw [hd'c1]
                rcases hcol_adj with hadj | hadj
                · omega
                · omega
              have hd'c2_eq : d'.cell2 = d.cell1 := by
                ext <;> [exact hd'c2_col.trans hc1_col.symm; exact hd'c2_row]
              by_cases hdd' : d = d'
              · rw [hdd'] at hmin2
                have : d'.minCol = 1 := hd'_min_eq
                simp only [Domino.minCol] at this hmin2
                omega
              · have hd_cov : d.cell1 ∈ d.cells := by simp [Domino.cells]
                have hd'_cov' : d.cell1 ∈ d'.cells := by simp [Domino.cells, hd'c2_eq]
                have hdisj := T.pairwise_disjoint d hd d' hd'_mem hdd'
                rw [Finset.disjoint_iff_ne] at hdisj
                exact absurd rfl (hdisj d.cell1 hd_cov d.cell1 hd'_cov')
            · have hd'c2 : d'.cell2 = (1, d.cell1.2) := hcov.symm
              have hd'c1_row : d'.cell1.2 = d.cell1.2 := by
                have h2 : d'.cell2.2 = d.cell1.2 := by rw [hd'c2]
                exact hrow_eq.trans h2
              have hd'c1_col : d'.cell1.1 = 2 := by
                have h2 : d'.cell2.1 = 1 := by rw [hd'c2]
                rcases hcol_adj with hadj | hadj
                · omega
                · omega
              have hd'c1_eq : d'.cell1 = d.cell1 := by
                ext <;> [exact hd'c1_col.trans hc1_col.symm; exact hd'c1_row]
              by_cases hdd' : d = d'
              · rw [hdd'] at hmin2
                have : d'.minCol = 1 := hd'_min_eq
                simp only [Domino.minCol] at this hmin2
                omega
              · have hd_cov : d.cell1 ∈ d.cells := by simp [Domino.cells]
                have hd'_cov' : d.cell1 ∈ d'.cells := by simp [Domino.cells, hd'c1_eq]
                have hdisj := T.pairwise_disjoint d hd d' hd'_mem hdd'
                rw [Finset.disjoint_iff_ne] at hdisj
                exact absurd rfl (hdisj d.cell1 hd_cov d.cell1 hd'_cov')
        · -- d.cell2 is in column 2 (similar argument)
          have h1r : (1, d.cell2.2) ∈ Rectangle n 3 := by
            rw [mem_Rectangle]
            exact ⟨le_refl 1, by omega, hc2_in_rect.2.2.1, hc2_in_rect.2.2.2⟩
          obtain ⟨d', hd'_mem, hd'_cov⟩ := T.cell_covered (1, d.cell2.2) h1r
          have hd'_min_le : d'.minCol ≤ 1 := by
            unfold Domino.minCol
            simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
            rcases hd'_cov with h | h
            · simp only [← h]; exact min_le_left _ _
            · simp only [← h]; exact min_le_right _ _
          have hd'_in_rect := T.dominos_in_rect d' hd'_mem
          have hd'_c1_in : d'.cell1 ∈ Rectangle n 3 := hd'_in_rect (by simp [Domino.cells])
          have hd'_c2_in : d'.cell2 ∈ Rectangle n 3 := hd'_in_rect (by simp [Domino.cells])
          rw [mem_Rectangle] at hd'_c1_in hd'_c2_in
          have hd'_col1_ge : d'.cell1.1 ≥ 1 := hd'_c1_in.1
          have hd'_col2_ge : d'.cell2.1 ≥ 1 := hd'_c2_in.1
          have hd'_min_eq : d'.minCol = 1 := by unfold Domino.minCol at hd'_min_le ⊢; omega
          have hd'_cov1 : ∃ y, (1, y) ∈ d'.cells := by
            unfold Domino.minCol at hd'_min_eq
            by_cases h : d'.cell1.1 ≤ d'.cell2.1
            · simp only [min_eq_left h] at hd'_min_eq
              exact ⟨d'.cell1.2, by simp [Domino.cells]; left; rw [← hd'_min_eq]⟩
            · push Not at h
              simp only [min_eq_right (le_of_lt h)] at hd'_min_eq
              exact ⟨d'.cell2.2, by simp [Domino.cells]; right; rw [← hd'_min_eq]⟩
          have hd'_novert : ¬d'.isVertical := by
            intro hvert
            apply hno_vert
            unfold DominoTiling.hasVerticalInCol
            obtain ⟨y, hy⟩ := hd'_cov1
            simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with h | h
            · exact ⟨d', hd'_mem, hvert, by rw [← h]⟩
            · have hc2' : d'.cell2.1 = 1 := by rw [← h]
              exact ⟨d', hd'_mem, hvert, by unfold Domino.isVertical at hvert; omega⟩
          unfold Domino.isVertical at hd'_novert
          rcases d'.adjacent with ⟨hcol_eq, _⟩ | ⟨hrow_eq, hcol_adj⟩
          · exact absurd hcol_eq hd'_novert
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
            rcases hd'_cov with hcov | hcov
            · have hd'c1 : d'.cell1 = (1, d.cell2.2) := hcov.symm
              have hd'c2_row : d'.cell2.2 = d.cell2.2 := by
                have h1 : d'.cell1.2 = d.cell2.2 := by rw [hd'c1]
                exact hrow_eq.symm.trans h1
              have hd'c2_col : d'.cell2.1 = 2 := by
                have h1 : d'.cell1.1 = 1 := by rw [hd'c1]
                rcases hcol_adj with hadj | hadj
                · omega
                · omega
              have hd'c2_eq : d'.cell2 = d.cell2 := by
                ext <;> [exact hd'c2_col.trans hc2_col.symm; exact hd'c2_row]
              by_cases hdd' : d = d'
              · rw [hdd'] at hmin2
                have : d'.minCol = 1 := hd'_min_eq
                simp only [Domino.minCol] at this hmin2
                omega
              · have hd_cov : d.cell2 ∈ d.cells := by simp [Domino.cells]
                have hd'_cov' : d.cell2 ∈ d'.cells := by simp [Domino.cells, hd'c2_eq]
                have hdisj := T.pairwise_disjoint d hd d' hd'_mem hdd'
                rw [Finset.disjoint_iff_ne] at hdisj
                exact absurd rfl (hdisj d.cell2 hd_cov d.cell2 hd'_cov')
            · have hd'c2 : d'.cell2 = (1, d.cell2.2) := hcov.symm
              have hd'c1_row : d'.cell1.2 = d.cell2.2 := by
                have h2 : d'.cell2.2 = d.cell2.2 := by rw [hd'c2]
                exact hrow_eq.trans h2
              have hd'c1_col : d'.cell1.1 = 2 := by
                have h2 : d'.cell2.1 = 1 := by rw [hd'c2]
                rcases hcol_adj with hadj | hadj
                · omega
                · omega
              have hd'c1_eq : d'.cell1 = d.cell2 := by
                ext <;> [exact hd'c1_col.trans hc2_col.symm; exact hd'c1_row]
              by_cases hdd' : d = d'
              · rw [hdd'] at hmin2
                have : d'.minCol = 1 := hd'_min_eq
                simp only [Domino.minCol] at this hmin2
                omega
              · have hd_cov : d.cell2 ∈ d.cells := by simp [Domino.cells]
                have hd'_cov' : d.cell2 ∈ d'.cells := by simp [Domino.cells, hd'c1_eq]
                have hdisj := T.pairwise_disjoint d hd d' hd'_mem hdd'
                rw [Finset.disjoint_iff_ne] at hdisj
                exact absurd rfl (hdisj d.cell2 hd_cov d.cell2 hd'_cov')
    exact hfree 2 (by omega) hn_ge_3 hfault

/-- The complete classification of faultfree domino tilings of height-3 rectangles.

    Every faultfree tiling of R_{n,3} is one of:
    - Equivalent to A_n for some even n ≥ 2 (vertical domino in top of column 1)
    - Equivalent to B_n for some even n ≥ 2 (vertical domino in bottom of column 1)
    - Equivalent to C (n = 2, no vertical domino in column 1)

    Note: We use TilingEquiv instead of = because the Domino structure
    distinguishes between different cell orderings.

    Note: requires n ≥ 1 (for n = 0, the empty tiling is a counterexample).

    (prop.gf.weighted-set.domino.Rn3.ABC) -/

lemma faultfree_classification (n : ℕ) (T : DominoTiling n 3) (hfree : T.isFaultfree)
    (hn : n ≥ 1) :
    (∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingA n hn hn_ge)) ∨
    (∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingB n hn hn_ge)) ∨
    (n = 2 ∧ ¬T.hasVerticalInCol 1 ∧ ∃ h : n = 2,
      DominoTiling.TilingEquiv (h ▸ T) TilingC) := by
  by_cases hvert : T.hasVerticalInCol 1
  · -- There is a vertical domino in column 1
    rcases vertical_in_col1_trichotomy n T hvert with htop | hbot
    · -- Top vertical case: T is some A_n
      left
      exact (faultfree_top_vertical_classification n T hfree htop).2
    · -- Bottom vertical case: T is some B_n
      right; left
      exact (faultfree_bottom_vertical_classification n T hfree hbot).2
  · -- No vertical domino in column 1: T is equivalent to C and n = 2
    right; right
    have hn2 : n = 2 := no_vertical_implies_n_eq_2 n T hfree hvert hn
    subst hn2
    exact ⟨rfl, hvert, rfl, faultfree_no_vertical_unique T hfree hvert⟩

end DominoTilings
end


/-!
# DominoTilings

Full-proof ports live under lemmaPath `Lemma/Nat/…` paths.
-/

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma x_shiftNeg_cell1
-- given
  (d : Domino)
  (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1)
  (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  (d.shiftNeg k h0 h1).cell1 = (d.cell1.1 - k, d.cell1.2) := by
-- proof
  apply DominoTilings.Domino.shiftNeg_cell1 d k h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma x_shiftNeg_cell2
-- given
  (d : Domino)
  (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1)
  (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  (d.shiftNeg k h0 h1).cell2 = (d.cell2.1 - k, d.cell2.2) := by
-- proof
  apply DominoTilings.Domino.shiftNeg_cell2 d k h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma x_vertical_1_1_cell2 :
-- imply
  vertical_1_1.cell2 = (1, 2) := by
-- proof
  apply DominoTilings.vertical_1_1_cell2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma x_horizontal_1_1_cell2 :
-- imply
  horizontal_1_1.cell2 = (2, 1) := by
-- proof
  apply DominoTilings.horizontal_1_1_cell2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma x_horizontal_1_2_cell2 :
-- imply
  horizontal_1_2.cell2 = (2, 2) := by
-- proof
  apply DominoTilings.horizontal_1_2_cell2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma x_vertical_1_1_isVertical :
-- imply
  vertical_1_1.isVertical := by
-- proof
  apply DominoTilings.vertical_1_1_isVertical

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma x_horizontal_1_1_isHorizontal :
-- imply
  horizontal_1_1.isHorizontal := by
-- proof
  apply DominoTilings.horizontal_1_1_isHorizontal

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma x_horizontal_1_2_isHorizontal :
-- imply
  horizontal_1_2.isHorizontal := by
-- proof
  apply DominoTilings.horizontal_1_2_isHorizontal

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_mem_Rectangle
  {n m : ℕ}
  {c : Cell} :
-- imply
  c ∈ Rectangle n m ↔ c.1 ≥ 1 ∧ c.1 ≤ n ∧ c.2 ≥ 1 ∧ c.2 ≤ m := by
-- proof
  apply DominoTilings.mem_Rectangle

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNat_cell1
-- given
  (d : Domino)
  (k : ℕ) :
-- imply
  (d.shiftNat k).cell1 = (d.cell1.1 + k, d.cell1.2) := by
-- proof
  apply DominoTilings.Domino.shiftNat_cell1 d k

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNat_cell2
-- given
  (d : Domino)
  (k : ℕ) :
-- imply
  (d.shiftNat k).cell2 = (d.cell2.1 + k, d.cell2.2) := by
-- proof
  apply DominoTilings.Domino.shiftNat_cell2 d k

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_cell1 :
-- imply
  vertical_1_1.cell1 = (1, 1) := by
-- proof
  apply DominoTilings.vertical_1_1_cell1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontal_1_1_cell1 :
-- imply
  horizontal_1_1.cell1 = (1, 1) := by
-- proof
  apply DominoTilings.horizontal_1_1_cell1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontal_1_2_cell1 :
-- imply
  horizontal_1_2.cell1 = (1, 2) := by
-- proof
  apply DominoTilings.horizontal_1_2_cell1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_cells :
-- imply
  vertical_1_1.cells = {(1, 1), (1, 2)} := by
-- proof
  apply DominoTilings.vertical_1_1_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_domino_cells_col_ge_one
  {n m : ℕ}
-- given
  (T : DominoTiling n m)
  (d : Domino)
  (hd : d ∈ T.dominos) :
-- imply
  d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1 := by
-- proof
  apply DominoTilings.DominoTiling.domino_cells_col_ge_one T d hd

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_other_dominos_col_ge_3
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2)
  (d : Domino)
  (hh1 : horizontal_1_1 ∈ T.dominos)
  (hh2 : horizontal_1_2 ∈ T.dominos)
  (hd : d ∈ T.dominos)
  (hne1 : d ≠ horizontal_1_1)
  (hne2 : d ≠ horizontal_1_2) :
-- imply
  d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
-- proof
  apply DominoTilings.DominoTiling.other_dominos_col_ge_3 T hh1 hh2 d hd hne1 hne2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_domino_col_ge_two_of_disjoint_from_first_col
  {n : ℕ}
-- given
  (T : DominoTiling (n + 1) 2)
  (v d : Domino)
  (hv : v ∈ T.dominos)
  (hv_cells : v.cells = vertical_1_1.cells)
  (hd : d ∈ T.dominos)
  (hne : d ≠ v) :
-- imply
  d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
-- proof
  apply DominoTilings.DominoTiling.domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d hd hne

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_domino_col_ge_two_of_ne_vertical
  {n : ℕ}
-- given
  (T : DominoTiling (n + 1) 2)
  (d : Domino)
  (hv : vertical_1_1 ∈ T.dominos)
  (hd : d ∈ T.dominos)
  (hne : d ≠ vertical_1_1) :
-- imply
  d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
-- proof
  apply DominoTilings.DominoTiling.domino_col_ge_two_of_ne_vertical T hv d hd hne

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_exists_domino_covering_11
  {n : ℕ}
-- given
  (T : DominoTiling (n + 1) 2) :
-- imply
  ∃ d ∈ T.dominos, (1, 1) ∈ d.cells := by
-- proof
  apply DominoTilings.DominoTiling.exists_domino_covering_11 T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_domino_covering_11_cells
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2)
  (d : Domino)
  (hd : d ∈ T.dominos)
  (hcov : (1, 1) ∈ d.cells) :
-- imply
  d.cells = {(1, 1), (1, 2)} ∨ d.cells = {(1, 1), (2, 1)} := by
-- proof
  apply DominoTilings.DominoTiling.domino_covering_11_cells T d hd hcov

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_exists_domino_covering_12_of_horizontal
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2)
  (d : Domino)
  (hd : d ∈ T.dominos)
  (hcells : d.cells = {(1, 1), (2, 1)}) :
-- imply
  ∃ d' ∈ T.dominos, d' ≠ d ∧ (1, 2) ∈ d'.cells := by
-- proof
  apply DominoTilings.DominoTiling.exists_domino_covering_12_of_horizontal T d hd hcells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_domino_covering_12_cells
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2)
  (d d' : Domino)
  (hd : d ∈ T.dominos)
  (hd' : d' ∈ T.dominos)
  (hne : d' ≠ d)
  (hd_cells : d.cells = {(1, 1), (2, 1)})
  (hd'_cov : (1, 2) ∈ d'.cells) :
-- imply
  d'.cells = {(1, 2), (2, 2)} := by
-- proof
  apply DominoTilings.DominoTiling.domino_covering_12_cells T d d' hd hd' hne hd_cells hd'_cov

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_other_dominos_col_ge_3_gen
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2)
  (d1 d2 d : Domino)
  (hd1 : d1 ∈ T.dominos)
  (hd2 : d2 ∈ T.dominos)
  (hd1_cells : d1.cells = ({(1, 1), (2, 1)} : Finset Cell))
  (hd2_cells : d2.cells = ({(1, 2), (2, 2)} : Finset Cell))
  (hd : d ∈ T.dominos)
  (hne1 : d ≠ d1)
  (hne2 : d ≠ d2) :
-- imply
  d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
-- proof
  apply DominoTilings.DominoTiling.other_dominos_col_ge_3_gen T d1 d2 hd1 hd2 hd1_cells hd2_cells d hd hne1 hne2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_hasVerticalFirstColumn_or_horizontalPair
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2) :
-- imply
  hasVerticalFirstColumn T ∨ (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧ (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
-- proof
  apply DominoTilings.DominoTiling.hasVerticalFirstColumn_or_horizontalPair T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontalPair_of_not_hasVerticalFirstColumn
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2)
  (hnotvert : ¬hasVerticalFirstColumn T) :
-- imply
  (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧ (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
-- proof
  apply DominoTilings.DominoTiling.horizontalPair_of_not_hasVerticalFirstColumn T hnotvert

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_card_Rectangle
-- given
  (n m : ℕ) :
-- imply
  (Rectangle n m).card = n * m := by
-- proof
  apply DominoTilings.card_Rectangle n m

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_card_cells
-- given
  (d : Domino) :
-- imply
  d.cells.card = 2 := by
-- proof
  apply DominoTilings.Domino.card_cells d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_isHorizontal_or_isVertical
-- given
  (d : Domino) :
-- imply
  d.isHorizontal ∨ d.isVertical := by
-- proof
  apply DominoTilings.Domino.isHorizontal_or_isVertical d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_not_isHorizontal_and_isVertical
-- given
  (d : Domino) :
-- imply
  ¬(d.isHorizontal ∧ d.isVertical) := by
-- proof
  apply DominoTilings.Domino.not_isHorizontal_and_isVertical d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_isHorizontal_iff_not_isVertical
-- given
  (d : Domino) :
-- imply
  d.isHorizontal ↔ ¬d.isVertical := by
-- proof
  apply DominoTilings.Domino.isHorizontal_iff_not_isVertical d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_isVertical_iff_not_isHorizontal
-- given
  (d : Domino) :
-- imply
  d.isVertical ↔ ¬d.isHorizontal := by
-- proof
  apply DominoTilings.Domino.isVertical_iff_not_isHorizontal d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_isHorizontal_xor_isVertical
-- given
  (d : Domino) :
-- imply
  Xor d.isHorizontal d.isVertical := by
-- proof
  apply DominoTilings.Domino.isHorizontal_xor_isVertical d

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNeg_shiftNat
-- given
  (d : Domino)
  (hc1 : d.cell1.1 ≥ 1)
  (hc2 : d.cell2.1 ≥ 1)
  (k : ℕ) :
-- imply
  (d.shiftNat k).shiftNeg k (by simp [shiftNat]; omega) (by simp [shiftNat]; omega) = d := by
-- proof
  apply DominoTilings.Domino.shiftNeg_shiftNat d k hc1 hc2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNat_shiftNeg
-- given
  (d : Domino)
  (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1)
  (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  (d.shiftNeg k h0 h1).shiftNat k = d := by
-- proof
  apply DominoTilings.Domino.shiftNat_shiftNeg d k h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNat_shiftNeg_cells
-- given
  (d : Domino)
  (k : ℕ)
  (h0 : d.cell1.1 ≥ k + 1)
  (h1 : d.cell2.1 ≥ k + 1) :
-- imply
  ((d.shiftNeg k h0 h1).shiftNat k).cells = d.cells := by
-- proof
  apply DominoTilings.Domino.shiftNat_shiftNeg_cells d k h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNat_injective
-- given
  (k : ℕ) :
-- imply
  Function.Injective (fun d : Domino => d.shiftNat k) := by
-- proof
  apply DominoTilings.Domino.shiftNat_injective k

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNeg_injective
  {d1 d2 : Domino}
  {k : ℕ}
-- given
  (h1_1 : d1.cell1.1 ≥ k + 1)
  (h1_2 : d1.cell2.1 ≥ k + 1)
  (h2_1 : d2.cell1.1 ≥ k + 1)
  (h2_2 : d2.cell2.1 ≥ k + 1)
  (heq : d1.shiftNeg k h1_1 h1_2 = d2.shiftNeg k h2_1 h2_2) :
-- imply
  d1 = d2 := by
-- proof
  apply DominoTilings.Domino.shiftNeg_injective h1_1 h1_2 h2_1 h2_2 heq

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNat_minCol_ge
-- given
  (d : Domino)
  (hc1 : d.cell1.1 ≥ 1)
  (hc2 : d.cell2.1 ≥ 1)
  (k : ℕ) :
-- imply
  (d.shiftNat k).minCol ≥ k + 1 := by
-- proof
  apply DominoTilings.Domino.shiftNat_minCol_ge d k hc1 hc2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNat_isVertical
-- given
  (d : Domino)
  (h : d.isVertical)
  (k : ℕ) :
-- imply
  (d.shiftNat k).isVertical := by
-- proof
  apply DominoTilings.Domino.shiftNat_isVertical d k h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_shiftNat_isHorizontal
-- given
  (d : Domino)
  (h : d.isHorizontal)
  (k : ℕ) :
-- imply
  (d.shiftNat k).isHorizontal := by
-- proof
  apply DominoTilings.Domino.shiftNat_isHorizontal d k h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontal_1_1_cells :
-- imply
  horizontal_1_1.cells = {(1, 1), (2, 1)} := by
-- proof
  apply DominoTilings.horizontal_1_1_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontal_1_2_cells :
-- imply
  horizontal_1_2.cells = {(1, 2), (2, 2)} := by
-- proof
  apply DominoTilings.horizontal_1_2_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_ne_horizontal_1_1 :
-- imply
  vertical_1_1 ≠ horizontal_1_1 := by
-- proof
  apply DominoTilings.vertical_1_1_ne_horizontal_1_1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_ne_horizontal_1_2 :
-- imply
  vertical_1_1 ≠ horizontal_1_2 := by
-- proof
  apply DominoTilings.vertical_1_1_ne_horizontal_1_2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontal_1_1_ne_horizontal_1_2 :
-- imply
  horizontal_1_1 ≠ horizontal_1_2 := by
-- proof
  apply DominoTilings.horizontal_1_1_ne_horizontal_1_2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_flip_cell1 :
-- imply
  vertical_1_1_flip.cell1 = (1, 2) := by
-- proof
  apply DominoTilings.vertical_1_1_flip_cell1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_flip_cell2 :
-- imply
  vertical_1_1_flip.cell2 = (1, 1) := by
-- proof
  apply DominoTilings.vertical_1_1_flip_cell2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_flip_cells :
-- imply
  vertical_1_1_flip.cells = {(1, 2), (1, 1)} := by
-- proof
  apply DominoTilings.vertical_1_1_flip_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_flip_cells_eq :
-- imply
  vertical_1_1_flip.cells = vertical_1_1.cells := by
-- proof
  apply DominoTilings.vertical_1_1_flip_cells_eq

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_ne_vertical_1_1_flip :
-- imply
  vertical_1_1 ≠ vertical_1_1_flip := by
-- proof
  apply DominoTilings.vertical_1_1_ne_vertical_1_1_flip

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_eq_vertical_1_1_of_cells_eq
-- given
  (d : Domino)
  (h : d.cells = vertical_1_1.cells) :
-- imply
  d = vertical_1_1 ∨ d = vertical_1_1_flip := by
-- proof
  apply DominoTilings.eq_vertical_1_1_of_cells_eq d h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_not_in_shiftNat1_image
-- given
  (S : Finset Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  vertical_1_1 ∉ S.image (fun d => d.shiftNat 1) := by
-- proof
  apply DominoTilings.vertical_1_1_not_in_shiftNat1_image S hS

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontal_1_1_not_in_shiftNat2_image
-- given
  (S : Finset Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  horizontal_1_1 ∉ S.image (fun d => d.shiftNat 2) := by
-- proof
  apply DominoTilings.horizontal_1_1_not_in_shiftNat2_image S hS

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontal_1_2_not_in_shiftNat2_image
-- given
  (S : Finset Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  horizontal_1_2 ∉ S.image (fun d => d.shiftNat 2) := by
-- proof
  apply DominoTilings.horizontal_1_2_not_in_shiftNat2_image S hS

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_not_in_shiftNat2_image
-- given
  (S : Finset Domino)
  (hS : ∀ d ∈ S, d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1) :
-- imply
  vertical_1_1 ∉ S.image (fun d => d.shiftNat 2) := by
-- proof
  apply DominoTilings.vertical_1_1_not_in_shiftNat2_image S hS

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_domino_cells_row_ge_one
  {n m : ℕ}
-- given
  (T : DominoTiling n m)
  (d : Domino)
  (hd : d ∈ T.dominos) :
-- imply
  d.cell1.2 ≥ 1 ∧ d.cell2.2 ≥ 1 := by
-- proof
  apply DominoTilings.DominoTiling.domino_cells_row_ge_one T d hd

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_card_eq_twice_dominos
  {n m : ℕ}
-- given
  (T : DominoTiling n m) :
-- imply
  (Rectangle n m).card = 2 * T.dominos.card := by
-- proof
  apply DominoTilings.DominoTiling.card_eq_twice_dominos T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_cell_covered
  {n m : ℕ}
-- given
  (c : Cell)
  (hc : c ∈ Rectangle n m)
  (T : DominoTiling n m) :
-- imply
  ∃ d ∈ T.dominos, c ∈ d.cells := by
-- proof
  apply DominoTilings.DominoTiling.cell_covered T c hc

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_cell_covered_unique
  {n m : ℕ}
-- given
  (T : DominoTiling n m)
  (c : Cell)
  (d₁ d₂ : Domino)
  (hd₁ : d₁ ∈ T.dominos)
  (hd₂ : d₂ ∈ T.dominos)
  (hc₁ : c ∈ d₁.cells)
  (hc₂ : c ∈ d₂.cells) :
-- imply
  d₁ = d₂ := by
-- proof
  apply DominoTilings.DominoTiling.cell_covered_unique T c d₁ d₂ hd₁ hd₂ hc₁ hc₂

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_tilingEquiv_refl
  {n m : ℕ}
-- given
  (T : DominoTiling n m) :
-- imply
  TilingEquiv T T := by
-- proof
  apply DominoTilings.DominoTiling.tilingEquiv_refl T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_tilingEquiv_symm
  {n m : ℕ}
  {T₁ T₂ : DominoTiling n m}
-- given
  (h : TilingEquiv T₁ T₂) :
-- imply
  TilingEquiv T₂ T₁ := by
-- proof
  apply DominoTilings.DominoTiling.tilingEquiv_symm h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_tilingEquiv_trans
  {n m : ℕ}
  {T₁ T₂ T₃ : DominoTiling n m}
-- given
  (h₀ : TilingEquiv T₁ T₂)
  (h₁ : TilingEquiv T₂ T₃) :
-- imply
  TilingEquiv T₁ T₃ := by
-- proof
  apply DominoTilings.DominoTiling.tilingEquiv_trans h₀ h₁

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_image_erase_insert_eq
  [DecidableEq α]
  [DecidableEq β]
-- given
  (S : Finset α)
  (v w : α)
  (f : α → β)
  (hv : v ∈ S)
  (hf : f v = f w) :
-- imply
  (insert w (S.erase v)).image f = S.image f := by
-- proof
  apply DominoTilings.DominoTiling.image_erase_insert_eq S v w f hv hf

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_restrictAfterVertical_prependVertical
  {n : ℕ}
-- given
  (T : DominoTiling n 2) :
-- imply
  restrictAfterVertical (prependVertical T) (by simp [prependVertical, vertical_1_1]) = T := by
-- proof
  apply DominoTilings.DominoTiling.restrictAfterVertical_prependVertical T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_prependVertical_restrictAfterVertical
  {n : ℕ}
-- given
  (T : DominoTiling (n + 1) 2)
  (hv : vertical_1_1 ∈ T.dominos) :
-- imply
  prependVertical (restrictAfterVertical T hv) = T := by
-- proof
  apply DominoTilings.DominoTiling.prependVertical_restrictAfterVertical T hv

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_restrictAfterHorizontalPair_prependHorizontalPair
  {n : ℕ}
-- given
  (T : DominoTiling n 2) :
-- imply
  restrictAfterHorizontalPair (prependHorizontalPair T) (by simp [prependHorizontalPair, horizontal_1_1]) (by simp [prependHorizontalPair, horizontal_1_2]) = T := by
-- proof
  apply DominoTilings.DominoTiling.restrictAfterHorizontalPair_prependHorizontalPair T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_prependHorizontalPair_restrictAfterHorizontalPair
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2)
  (hh1 : horizontal_1_1 ∈ T.dominos)
  (hh2 : horizontal_1_2 ∈ T.dominos) :
-- imply
  prependHorizontalPair (restrictAfterHorizontalPair T hh1 hh2) = T := by
-- proof
  apply DominoTilings.DominoTiling.prependHorizontalPair_restrictAfterHorizontalPair T hh1 hh2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_restrictAfterVerticalGen_eq_restrictAfterVertical
  {n : ℕ}
-- given
  (T : DominoTiling (n + 1) 2)
  (hv : vertical_1_1 ∈ T.dominos) :
-- imply
  restrictAfterVerticalGen T vertical_1_1 hv rfl = restrictAfterVertical T hv := by
-- proof
  apply DominoTilings.DominoTiling.restrictAfterVerticalGen_eq_restrictAfterVertical T hv

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_or_flip_of_hasVerticalFirstColumn
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2)
  (hvert : hasVerticalFirstColumn T) :
-- imply
  vertical_1_1 ∈ T.dominos ∨ vertical_1_1_flip ∈ T.dominos := by
-- proof
  apply DominoTilings.DominoTiling.vertical_1_1_or_flip_of_hasVerticalFirstColumn T hvert

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_flip_not_mem_of_vertical_1_1_mem
  {n m : ℕ}
-- given
  (T : DominoTiling n m)
  (hv : vertical_1_1 ∈ T.dominos) :
-- imply
  vertical_1_1_flip ∉ T.dominos := by
-- proof
  apply DominoTilings.DominoTiling.vertical_1_1_flip_not_mem_of_vertical_1_1_mem T hv

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_classical_choose_hasVerticalFirstColumn_eq_vertical_1_1
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2)
  (hv_mem : vertical_1_1 ∈ T.dominos)
  (hv : hasVerticalFirstColumn T) :
-- imply
  Classical.choose hv = vertical_1_1 := by
-- proof
  apply DominoTilings.DominoTiling.classical_choose_hasVerticalFirstColumn_eq_vertical_1_1 T hv_mem hv

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontal_1_1_unique_in_prependHorizontalPair
  {n : ℕ}
-- given
  (T : DominoTiling n 2)
  (d : Domino)
  (hd : d ∈ (prependHorizontalPair T).dominos)
  (hd_cells : d.cells = ({(1, 1), (2, 1)} : Finset Cell)) :
-- imply
  d = horizontal_1_1 := by
-- proof
  apply DominoTilings.DominoTiling.horizontal_1_1_unique_in_prependHorizontalPair T d hd hd_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_horizontal_1_2_unique_in_prependHorizontalPair
  {n : ℕ}
-- given
  (T : DominoTiling n 2)
  (d : Domino)
  (hd : d ∈ (prependHorizontalPair T).dominos)
  (hd_cells : d.cells = ({(1, 2), (2, 2)} : Finset Cell)) :
-- imply
  d = horizontal_1_2 := by
-- proof
  apply DominoTilings.DominoTiling.horizontal_1_2_unique_in_prependHorizontalPair T d hd hd_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_1_1_unique_in_prependVertical
  {n : ℕ}
-- given
  (T : DominoTiling n 2)
  (d : Domino)
  (hd : d ∈ (prependVertical T).dominos)
  (hd_cells : d.cells = ({(1, 1), (1, 2)} : Finset Cell)) :
-- imply
  d = vertical_1_1 := by
-- proof
  apply DominoTilings.DominoTiling.vertical_1_1_unique_in_prependVertical T d hd hd_cells

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_tiling_2_to_sum_from_sum
  {n : ℕ}
-- given
  (x : (DominoTiling n 2) ⊕ (DominoTiling (n + 1) 2)) :
-- imply
  tiling_2_to_sum (tiling_2_from_sum x) = x := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_to_sum_from_sum x

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_tiling_2_to_sum_surjective
  {n : ℕ} :
-- imply
  Function.Surjective (@tiling_2_to_sum n) := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_to_sum_surjective

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_tiling_2_from_sum_injective
  {n : ℕ} :
-- imply
  Function.Injective (@tiling_2_from_sum n) := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_from_sum_injective

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_tiling_2_roundtrip_TilingEquiv
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2) :
-- imply
  TilingEquiv (tiling_2_from_sum (tiling_2_to_sum T)) T := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_roundtrip_TilingEquiv T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_tiling_2_from_sum_surjective_up_to_TilingEquiv
  {n : ℕ}
-- given
  (T : DominoTiling (n + 2) 2) :
-- imply
  ∃ x, TilingEquiv (tiling_2_from_sum x) T := by
-- proof
  apply DominoTilings.DominoTiling.tiling_2_from_sum_surjective_up_to_TilingEquiv T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_mkHorizontalDomino_cell1
-- given
  (x y : ℕ) :
-- imply
  (mkHorizontalDomino x y).cell1 = (x, y) := by
-- proof
  apply DominoTilings.mkHorizontalDomino_cell1 x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_mkHorizontalDomino_cell2
-- given
  (x y : ℕ) :
-- imply
  (mkHorizontalDomino x y).cell2 = (x + 1, y) := by
-- proof
  apply DominoTilings.mkHorizontalDomino_cell2 x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_mkVerticalDomino_cell1
-- given
  (x y : ℕ) :
-- imply
  (mkVerticalDomino x y).cell1 = (x, y) := by
-- proof
  apply DominoTilings.mkVerticalDomino_cell1 x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_mkVerticalDomino_cell2
-- given
  (x y : ℕ) :
-- imply
  (mkVerticalDomino x y).cell2 = (x, y + 1) := by
-- proof
  apply DominoTilings.mkVerticalDomino_cell2 x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_isHorizontal_mkHorizontalDomino
-- given
  (x y : ℕ) :
-- imply
  (mkHorizontalDomino x y).isHorizontal := by
-- proof
  apply DominoTilings.isHorizontal_mkHorizontalDomino x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_isVertical_mkVerticalDomino
-- given
  (x y : ℕ) :
-- imply
  (mkVerticalDomino x y).isVertical := by
-- proof
  apply DominoTilings.isVertical_mkVerticalDomino x y

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_reflectCell3_involutive
-- given
  (c : Cell)
  (h0 : c.2 ≥ 1)
  (h1 : c.2 ≤ 3) :
-- imply
  reflectCell3 (reflectCell3 c) = c := by
-- proof
  apply DominoTilings.reflectCell3_involutive c h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_reflectTiling3_dominos_minCol_maxCol
  {n : ℕ}
-- given
  (T : DominoTiling n 3) :
-- imply
  ∀ d ∈ T.dominos, ∃ d' ∈ (reflectTiling3 T).dominos, d'.minCol = d.minCol ∧ d'.maxCol = d.maxCol := by
-- proof
  apply DominoTilings.reflectTiling3_dominos_minCol_maxCol T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_reflectTiling3_isFaultfree
  {n : ℕ}
-- given
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree) :
-- imply
  (reflectTiling3 T).isFaultfree := by
-- proof
  apply DominoTilings.reflectTiling3_isFaultfree T hfree

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_reflectTiling3_hasTopVertical_iff_hasBottomVertical
  {n : ℕ}
-- given
  (T : DominoTiling n 3)
  (c : ℕ) :
-- imply
  (reflectTiling3 T).hasTopVerticalInCol c ↔ T.hasBottomVerticalInCol c := by
-- proof
  apply DominoTilings.reflectTiling3_hasTopVertical_iff_hasBottomVertical T c

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_reflectTiling3_involutive
  {n : ℕ}
-- given
  (T : DominoTiling n 3) :
-- imply
  reflectTiling3 (reflectTiling3 T) = T := by
-- proof
  apply DominoTilings.reflectTiling3_involutive T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_reflectTiling3_preserves_TilingEquiv
  {n : ℕ}
-- given
  (T₁ T₂ : DominoTiling n 3)
  (h : DominoTiling.TilingEquiv T₁ T₂) :
-- imply
  DominoTiling.TilingEquiv (reflectTiling3 T₁) (reflectTiling3 T₂) := by
-- proof
  apply DominoTilings.reflectTiling3_preserves_TilingEquiv T₁ T₂ h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_TilingB_eq_reflectTiling3_TilingA
-- given
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  TilingB n hn hn_ge = reflectTiling3 (TilingA n hn hn_ge) := by
-- proof
  apply DominoTilings.TilingB_eq_reflectTiling3_TilingA n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_TilingA_isFaultfree
-- given
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  (TilingA n hn hn_ge).isFaultfree := by
-- proof
  apply DominoTilings.TilingA_isFaultfree n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_TilingB_isFaultfree
-- given
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  (TilingB n hn hn_ge).isFaultfree := by
-- proof
  apply DominoTilings.TilingB_isFaultfree n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_TilingC_isFaultfree :
-- imply
  TilingC.isFaultfree := by
-- proof
  apply DominoTilings.TilingC_isFaultfree

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_TilingA_hasTopVertical
-- given
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  (TilingA n hn hn_ge).hasTopVerticalInCol 1 := by
-- proof
  apply DominoTilings.TilingA_hasTopVertical n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_TilingB_hasBottomVertical
-- given
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  (TilingB n hn hn_ge).hasBottomVerticalInCol 1 := by
-- proof
  apply DominoTilings.TilingB_hasBottomVertical n hn hn_ge

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_TilingC_noVerticalInCol1 :
-- imply
  ¬TilingC.hasVerticalInCol 1 := by
-- proof
  apply DominoTilings.TilingC_noVerticalInCol1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_hasTopVerticalInCol_implies_n_ge
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (c : ℕ)
  (htop : T.hasTopVerticalInCol c) :
-- imply
  n ≥ c := by
-- proof
  apply DominoTilings.hasTopVerticalInCol_implies_n_ge n T c htop

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_rectangle_tileable_iff_even
-- given
  (n : ℕ) :
-- imply
  Nonempty (DominoTiling n 3) → Even n ∨ n = 0 := by
-- proof
  apply DominoTilings.rectangle_tileable_iff_even n

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_base_case_basement
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (htop : T.hasTopVerticalInCol 1)
  (hn : n ≥ 2) :
-- imply
  ∃ d ∈ T.dominos, d.cells = {(1, 1), (2, 1)} := by
-- proof
  apply DominoTilings.base_case_basement n T htop hn

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_claim1_basement_middle_top
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (i : ℕ)
  (hfree : T.isFaultfree)
  (htop : T.hasTopVerticalInCol 1)
  (hi_pos : i ≥ 1)
  (hi_lt : i < n / 2) :
-- imply
  (∃ d ∈ T.dominos, d.cells = {(2*i - 1, 1), (2*i, 1)}) ∧ (∃ d ∈ T.dominos, d.cells = {(2*i, 2), (2*i + 1, 2)}) ∧ (∃ d ∈ T.dominos, d.cells = {(2*i, 3), (2*i + 1, 3)}) := by
-- proof
  apply DominoTilings.claim1_basement_middle_top n T hfree htop i hi_pos hi_lt

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_claim2_n_even
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (htop : T.hasTopVerticalInCol 1) :
-- imply
  Even n := by
-- proof
  apply DominoTilings.claim2_n_even n T hfree htop

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_faultfree_hasTopVerticalInCol_implies_n_ge_two
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (htop : T.hasTopVerticalInCol 1) :
-- imply
  n ≥ 2 := by
-- proof
  apply DominoTilings.faultfree_hasTopVerticalInCol_implies_n_ge_two n T hfree htop

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_faultfree_no_vertical_unique
-- given
  (T : DominoTiling 2 3)
  (hfree : T.isFaultfree)
  (hno_vert : ¬T.hasVerticalInCol 1) :
-- imply
  DominoTiling.TilingEquiv T TilingC := by
-- proof
  apply DominoTilings.faultfree_no_vertical_unique T hfree hno_vert

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_faultfree_top_vertical_classification
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (htop : T.hasTopVerticalInCol 1) :
-- imply
  Even n ∧ ∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingA n hn hn_ge) := by
-- proof
  apply DominoTilings.faultfree_top_vertical_classification n T hfree htop

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_faultfree_bottom_vertical_classification
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (hbot : T.hasBottomVerticalInCol 1) :
-- imply
  Even n ∧ ∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingB n hn hn_ge) := by
-- proof
  apply DominoTilings.faultfree_bottom_vertical_classification n T hfree hbot

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_vertical_in_col1_trichotomy
-- given
  (n : ℕ)
  (T : DominoTiling n 3) :
-- imply
  T.hasVerticalInCol 1 → T.hasTopVerticalInCol 1 ∨ T.hasBottomVerticalInCol 1 := by
-- proof
  apply DominoTilings.vertical_in_col1_trichotomy n T

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_no_vertical_implies_n_eq_2
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (hno_vert : ¬T.hasVerticalInCol 1)
  (hn : n ≥ 1) :
-- imply
  n = 2 := by
-- proof
  apply DominoTilings.no_vertical_implies_n_eq_2 n T hfree hno_vert hn

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma dt_faultfree_classification
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (hn : n ≥ 1) :
-- imply
  (∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingA n hn hn_ge)) ∨ (∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingB n hn hn_ge)) ∨ (n = 2 ∧ ¬T.hasVerticalInCol 1 ∧ ∃ h : n = 2, DominoTiling.TilingEquiv (h ▸ T) TilingC) := by
-- proof
  apply DominoTilings.faultfree_classification n T hfree hn

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_nat_sub_inj_4
  {a b : ℕ}
-- given
  (ha : a ≤ 4)
  (hb : b ≤ 4)
  (h : 4 - a = 4 - b) :
-- imply
  a = b := by
-- proof
  apply DominoTilings.nat_sub_inj_4 ha hb h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_cell1_row_le'
  {n : ℕ}
  {d : Domino}
-- given
  (hd : d.cells ⊆ Rectangle n 3) :
-- imply
  d.cell1.2 ≤ 3 := by
-- proof
  apply DominoTilings.domino_cell1_row_le' hd

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_cell2_row_le'
  {n : ℕ}
  {d : Domino}
-- given
  (hd : d.cells ⊆ Rectangle n 3) :
-- imply
  d.cell2.2 ≤ 3 := by
-- proof
  apply DominoTilings.domino_cell2_row_le' hd

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_reflectDomino3_injective
  {d1 d2 : Domino}
-- given
  (h1a : d1.cell1.2 ≤ 3)
  (h1b : d1.cell2.2 ≤ 3)
  (h2a : d2.cell1.2 ≤ 3)
  (h2b : d2.cell2.2 ≤ 3)
  (heq : reflectDomino3 d1 h1a h1b = reflectDomino3 d2 h2a h2b) :
-- imply
  d1 = d2 := by
-- proof
  apply DominoTilings.reflectDomino3_injective h1a h1b h2a h2b heq

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_reflectCell3_mem_Rectangle'
  {n : ℕ}
  {c : Cell}
-- given
  (hc : c ∈ Rectangle n 3) :
-- imply
  reflectCell3 c ∈ Rectangle n 3 := by
-- proof
  apply DominoTilings.reflectCell3_mem_Rectangle' hc

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_reflectDomino3_cells
  {d : Domino}
-- given
  (h0 : d.cell1.2 ≤ 3)
  (h1 : d.cell2.2 ≤ 3) :
-- imply
  (reflectDomino3 d h0 h1).cells = d.cells.image reflectCell3 := by
-- proof
  apply DominoTilings.reflectDomino3_cells h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_reflectDomino3_cells_subset
  {n : ℕ}
  {d : Domino}
-- given
  (hd : d.cells ⊆ Rectangle n 3)
  (h0 : d.cell1.2 ≤ 3)
  (h1 : d.cell2.2 ≤ 3) :
-- imply
  (reflectDomino3 d h0 h1).cells ⊆ Rectangle n 3 := by
-- proof
  apply DominoTilings.reflectDomino3_cells_subset hd h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_reflectCell3_injective_on_rect
  {n : ℕ}
  {c1 c2 : Cell}
-- given
  (hc1 : c1 ∈ Rectangle n 3)
  (hc2 : c2 ∈ Rectangle n 3)
  (heq : reflectCell3 c1 = reflectCell3 c2) :
-- imply
  c1 = c2 := by
-- proof
  apply DominoTilings.reflectCell3_injective_on_rect hc1 hc2 heq

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_reflectCell3_surjective_on_rect
  {n : ℕ}
  {c : Cell}
-- given
  (hc : c ∈ Rectangle n 3) :
-- imply
  ∃ c' ∈ Rectangle n 3, reflectCell3 c' = c := by
-- proof
  apply DominoTilings.reflectCell3_surjective_on_rect hc

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_image_preserved_under_double_roundtrip'
  [DecidableEq α]
  [DecidableEq β]
  [DecidableEq γ]
-- given
  (S : Finset α)
  (g : β → α)
  (f : (x : α) → x ∈ S → β)
  (h : α → γ)
  (hfgh : ∀ x (hx : x ∈ S), h (g (f x hx)) = h x) :
-- imply
  ((S.attach.image (fun ⟨x, hx⟩ => f x hx)).image g).image h = S.image h := by
-- proof
  apply DominoTilings.DominoTiling.image_preserved_under_double_roundtrip' S f g h hfgh

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_insert_erase_image_eq'
  [DecidableEq α]
  [DecidableEq β]
-- given
  (S : Finset α)
  (v : α)
  (h : α → β)
  (hv : v ∈ S) :
-- imply
  insert (h v) ((S.erase v).image h) = S.image h := by
-- proof
  apply DominoTilings.DominoTiling.insert_erase_image_eq' S v h hv

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_insert_insert_erase_erase_image_eq
  [DecidableEq α]
  [DecidableEq β]
-- given
  (S : Finset α)
  (v1 v2 : α)
  (h : α → β)
  (hv1 : v1 ∈ S)
  (hv2 : v2 ∈ S) :
-- imply
  insert (h v1) (insert (h v2) (((S.erase v1).erase v2).image h)) = S.image h := by
-- proof
  apply DominoTilings.DominoTiling.insert_insert_erase_erase_image_eq S v1 v2 h hv1 hv2

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_cell1_row_ge'
  {n : ℕ}
  {d : Domino}
-- given
  (hd : d.cells ⊆ Rectangle n 3) :
-- imply
  d.cell1.2 ≥ 1 := by
-- proof
  apply DominoTilings.domino_cell1_row_ge' hd

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_cell2_row_ge'
  {n : ℕ}
  {d : Domino}
-- given
  (hd : d.cells ⊆ Rectangle n 3) :
-- imply
  d.cell2.2 ≥ 1 := by
-- proof
  apply DominoTilings.domino_cell2_row_ge' hd

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_reflectDomino3_minCol
  {d : Domino}
-- given
  (h0 : d.cell1.2 ≤ 3)
  (h1 : d.cell2.2 ≤ 3) :
-- imply
  (reflectDomino3 d h0 h1).minCol = d.minCol := by
-- proof
  apply DominoTilings.reflectDomino3_minCol h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_reflectDomino3_maxCol
  {d : Domino}
-- given
  (h0 : d.cell1.2 ≤ 3)
  (h1 : d.cell2.2 ≤ 3) :
-- imply
  (reflectDomino3 d h0 h1).maxCol = d.maxCol := by
-- proof
  apply DominoTilings.reflectDomino3_maxCol h0 h1

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_middleDominos_mem
-- given
  (n i : ℕ)
  (hi : i < n / 2 - 1) :
-- imply
  ∃ d ∈ middleDominos n, d.cell1 = (2 * i + 2, 2) ∧ d.cell2 = (2 * i + 3, 2) := by
-- proof
  apply DominoTilings.middleDominos_mem n i hi

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_basementDominos_mem
-- given
  (n i : ℕ)
  (hi : i < n / 2) :
-- imply
  ∃ d ∈ basementDominos n, d.cell1 = (2 * i + 1, 1) ∧ d.cell2 = (2 * i + 2, 1) := by
-- proof
  apply DominoTilings.basementDominos_mem n i hi

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_topDominos_mem
-- given
  (n i : ℕ)
  (hi : i < n / 2 - 1) :
-- imply
  ∃ d ∈ topDominos n, d.cell1 = (2 * i + 2, 3) ∧ d.cell2 = (2 * i + 3, 3) := by
-- proof
  apply DominoTilings.topDominos_mem n i hi

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_col_in_basement_range
-- given
  (n col : ℕ)
  (hn : Even n)
  (hcol_ge : col ≥ 1)
  (hcol_le : col ≤ n) :
-- imply
  ∃ i < n / 2, col = 2 * i + 1 ∨ col = 2 * i + 2 := by
-- proof
  apply DominoTilings.col_in_basement_range n col hn hcol_ge hcol_le

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_col_in_middle_range
-- given
  (n col : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2)
  (hcol_ge : col ≥ 2)
  (hcol_le : col ≤ n - 1) :
-- imply
  ∃ i < n / 2 - 1, col = 2 * i + 2 ∨ col = 2 * i + 3 := by
-- proof
  apply DominoTilings.col_in_middle_range n col hn hn_ge hcol_ge hcol_le

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_TilingA_row1_covered
-- given
  (n col : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2)
  (hcol_ge : col ≥ 1)
  (hcol_le : col ≤ n) :
-- imply
  ∃ d ∈ (TilingA n hn hn_ge).dominos, (col, 1) ∈ d.cells := by
-- proof
  apply DominoTilings.TilingA_row1_covered n col hn hn_ge hcol_ge hcol_le

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_TilingA_row2_covered
-- given
  (n col : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2)
  (hcol_ge : col ≥ 1)
  (hcol_le : col ≤ n) :
-- imply
  ∃ d ∈ (TilingA n hn hn_ge).dominos, (col, 2) ∈ d.cells := by
-- proof
  apply DominoTilings.TilingA_row2_covered n col hn hn_ge hcol_ge hcol_le

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_TilingA_row3_covered
-- given
  (n col : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2)
  (hcol_ge : col ≥ 1)
  (hcol_le : col ≤ n) :
-- imply
  ∃ d ∈ (TilingA n hn hn_ge).dominos, (col, 3) ∈ d.cells := by
-- proof
  apply DominoTilings.TilingA_row3_covered n col hn hn_ge hcol_ge hcol_le

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_at_22_options
-- given
  (n : ℕ)
  (d : Domino)
  (h_in : d.cells ⊆ Rectangle n 3)
  (h_cov : (2, 2) ∈ d.cells)
  (h_not_12 : (1, 2) ∉ d.cells) :
-- imply
  d.cells = {(2, 2), (3, 2)} ∨ d.cells = {(2, 1), (2, 2)} ∨ d.cells = {(2, 2), (2, 3)} := by
-- proof
  apply DominoTilings.domino_at_22_options n d h_in h_cov h_not_12

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_at_23_options
-- given
  (n : ℕ)
  (d : Domino)
  (h_in : d.cells ⊆ Rectangle n 3)
  (h_cov : (2, 3) ∈ d.cells)
  (h_not_13 : (1, 3) ∉ d.cells) :
-- imply
  d.cells = {(2, 3), (3, 3)} ∨ d.cells = {(2, 2), (2, 3)} := by
-- proof
  apply DominoTilings.domino_at_23_options n d h_in h_cov h_not_13

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_maxCol_eq_2_of_cells_eq_11_21
-- given
  (d : Domino)
  (h : d.cells = {(1, 1), (2, 1)}) :
-- imply
  d.maxCol = 2 := by
-- proof
  apply DominoTilings.maxCol_eq_2_of_cells_eq_11_21 d h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_minCol_maxCol_eq_2_of_cells_eq_22_23
-- given
  (d : Domino)
  (h : d.cells = {(2, 2), (2, 3)}) :
-- imply
  d.minCol = 2 ∧ d.maxCol = 2 := by
-- proof
  apply DominoTilings.minCol_maxCol_eq_2_of_cells_eq_22_23 d h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_minCol_maxCol_eq_2_of_cells_eq_21_22
-- given
  (d : Domino)
  (h : d.cells = {(2, 1), (2, 2)}) :
-- imply
  d.minCol = 2 ∧ d.maxCol = 2 := by
-- proof
  apply DominoTilings.minCol_maxCol_eq_2_of_cells_eq_21_22 d h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_at_c1_forced_right
-- given
  (n c : ℕ)
  (d : Domino)
  (hc_ge : c ≥ 1)
  (hc_lt : c < n)
  (h_in : d.cells ⊆ Rectangle n 3)
  (h_cov : (c, 1) ∈ d.cells)
  (h_not_left : (c - 1, 1) ∉ d.cells)
  (h_not_up : (c, 2) ∉ d.cells) :
-- imply
  d.cells = {(c, 1), (c + 1, 1)} := by
-- proof
  apply DominoTilings.domino_at_c1_forced_right n c d hc_ge hc_lt h_in h_cov h_not_left h_not_up

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_at_c2_options
-- given
  (n c : ℕ)
  (d : Domino)
  (hc_ge : c ≥ 1)
  (hc_lt : c < n)
  (h_in : d.cells ⊆ Rectangle n 3)
  (h_cov : (c, 2) ∈ d.cells)
  (h_not_left : (c - 1, 2) ∉ d.cells) :
-- imply
  d.cells = {(c, 2), (c + 1, 2)} ∨ d.cells = {(c, 1), (c, 2)} ∨ d.cells = {(c, 2), (c, 3)} := by
-- proof
  apply DominoTilings.domino_at_c2_options n c d hc_ge hc_lt h_in h_cov h_not_left

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_at_c3_options
-- given
  (n c : ℕ)
  (d : Domino)
  (hc_ge : c ≥ 1)
  (hc_lt : c < n)
  (h_in : d.cells ⊆ Rectangle n 3)
  (h_cov : (c, 3) ∈ d.cells)
  (h_not_left : (c - 1, 3) ∉ d.cells) :
-- imply
  d.cells = {(c, 3), (c + 1, 3)} ∨ d.cells = {(c, 2), (c, 3)} := by
-- proof
  apply DominoTilings.domino_at_c3_options n c d hc_ge hc_lt h_in h_cov h_not_left

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_minCol_maxCol_eq_c_of_cells_eq_c2_c3
-- given
  (c : ℕ)
  (d : Domino)
  (h : d.cells = {(c, 2), (c, 3)}) :
-- imply
  d.minCol = c ∧ d.maxCol = c := by
-- proof
  apply DominoTilings.minCol_maxCol_eq_c_of_cells_eq_c2_c3 c d h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_minCol_maxCol_eq_c_of_cells_eq_c1_c2
-- given
  (c : ℕ)
  (d : Domino)
  (h : d.cells = {(c, 1), (c, 2)}) :
-- imply
  d.minCol = c ∧ d.maxCol = c := by
-- proof
  apply DominoTilings.minCol_maxCol_eq_c_of_cells_eq_c1_c2 c d h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_maxCol_eq_c_add_1_of_cells_eq_c1_c_add_1_1
-- given
  (c : ℕ)
  (d : Domino)
  (h : d.cells = {(c, 1), (c + 1, 1)}) :
-- imply
  d.maxCol = c + 1 := by
-- proof
  apply DominoTilings.maxCol_eq_c_add_1_of_cells_eq_c1_c_add_1_1 c d h

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_at_n3_options
-- given
  (n : ℕ)
  (d : Domino)
  (h_in : d.cells ⊆ Rectangle n 3)
  (h_cov : (n, 3) ∈ d.cells) :
-- imply
  d.cells = {(n - 1, 3), (n, 3)} ∨ d.cells = {(n, 2), (n, 3)} := by
-- proof
  apply DominoTilings.domino_at_n3_options n d h_in h_cov

/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma pv_domino_at_n1_options
-- given
  (n : ℕ)
  (d : Domino)
  (h_in : d.cells ⊆ Rectangle n 3)
  (h_cov : (n, 1) ∈ d.cells) :
-- imply
  d.cells = {(n - 1, 1), (n, 1)} ∨ d.cells = {(n, 1), (n, 2)} := by
-- proof
  apply DominoTilings.domino_at_n1_options n d h_in h_cov


-- created on 2026-10-23
-- updated on 2026-10-28
