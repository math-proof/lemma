import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f g : ℕ → ℝ}
  {n : ℕ}
-- given
  (h : 0 < n) :
-- imply
  sSup ((fun i => max (f i) (g i)) '' (Finset.range n : Set ℕ))
    = max (sSup (f '' (Finset.range n : Set ℕ))) (sSup (g '' (Finset.range n : Set ℕ))) := by
-- proof
  have hS : (Finset.range n : Set ℕ).Nonempty := ⟨0, by simpa using h⟩
  have hfin : (Finset.range n : Set ℕ).Finite := Set.toFinite _
  have hA : BddAbove (f '' (Finset.range n : Set ℕ)) := hfin.image f |>.bddAbove
  have hB : BddAbove (g '' (Finset.range n : Set ℕ)) := hfin.image g |>.bddAbove
  have hC : BddAbove ((fun i => max (f i) (g i)) '' (Finset.range n : Set ℕ)) :=
    hfin.image _ |>.bddAbove
  apply le_antisymm
  ·
    apply csSup_le (hS.image _)
    rintro z ⟨i, hi, rfl⟩
    apply max_le_max (le_csSup hA (Set.mem_image_of_mem f hi)) (le_csSup hB (Set.mem_image_of_mem g hi))
  ·
    apply max_le
    ·
      apply csSup_le (hS.image f)
      rintro z ⟨i, hi, rfl⟩
      apply le_trans (le_max_left _ _) (le_csSup hC (Set.mem_image_of_mem _ hi))
    ·
      apply csSup_le (hS.image g)
      rintro z ⟨i, hi, rfl⟩
      apply le_trans (le_max_right _ _) (le_csSup hC (Set.mem_image_of_mem _ hi))


-- created on 2026-10-08
