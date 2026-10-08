import sympy.concrete.expr_with_limits
import sympy.Basic


@[main]
private lemma main
  {f g : ℕ → ℝ}
  {n : ℕ}
-- given
  (h : 0 < n) :
-- imply
  Minima (Finset.range n : Set ℕ) (fun i => min (f i) (g i))
    = min (Minima (Finset.range n : Set ℕ) f) (Minima (Finset.range n : Set ℕ) g) := by
-- proof
  simp only [Minima]
  have hS : (Finset.range n : Set ℕ).Nonempty := ⟨0, by simpa using h⟩
  have hfin : (Finset.range n : Set ℕ).Finite := Set.toFinite _
  have hA : BddBelow (f '' (Finset.range n : Set ℕ)) := hfin.image f |>.bddBelow
  have hB : BddBelow (g '' (Finset.range n : Set ℕ)) := hfin.image g |>.bddBelow
  have hC : BddBelow ((fun i => min (f i) (g i)) '' (Finset.range n : Set ℕ)) :=
    hfin.image _ |>.bddBelow
  apply le_antisymm
  ·
    apply le_min
    ·
      apply le_csInf (hS.image f)
      rintro z ⟨i, hi, rfl⟩
      apply le_trans (csInf_le hC (Set.mem_image_of_mem _ hi)) (min_le_left _ _)
    ·
      apply le_csInf (hS.image g)
      rintro z ⟨i, hi, rfl⟩
      apply le_trans (csInf_le hC (Set.mem_image_of_mem _ hi)) (min_le_right _ _)
  ·
    apply le_csInf (hS.image _)
    rintro z ⟨i, hi, rfl⟩
    apply min_le_min (csInf_le hA (Set.mem_image_of_mem f hi)) (csInf_le hB (Set.mem_image_of_mem g hi))


-- created on 2026-10-08
