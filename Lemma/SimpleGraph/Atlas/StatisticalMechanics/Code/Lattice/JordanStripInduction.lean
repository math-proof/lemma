import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanStripInduction.Part9
open Set SimpleGraph MeasureTheory StatMech StatMech.Lattice


/--
[jsi_adj_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_adj_cases_eq
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  (u 1 = v 1 ∧ (u 0 - v 0 = 1 ∨ u 0 - v 0 = -1)) ∨ (u 0 = v 0 ∧ (u 1 - v 1 = 1 ∨ u 1 - v 1 = -1)) := by
-- proof
  apply StatMech.Lattice.jsi_adj_cases u v hadj

/--
[jsi_cell_0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_cell_0_eq
  {k r : ℤ} :
-- imply
  jsi_cell k r 0 = k := by
-- proof
  apply StatMech.Lattice.jsi_cell_0 k r

/--
[jsi_cell_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_cell_1_eq
  {k r : ℤ} :
-- imply
  jsi_cell k r 1 = r := by
-- proof
  apply StatMech.Lattice.jsi_cell_1 k r

/--
[jsi_cell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_cell_eq_eq
  {k r k' r' : ℤ} :
-- imply
  jsi_cell k r = jsi_cell k' r' ↔ k = k' ∧ r = r' := by
-- proof
  apply StatMech.Lattice.jsi_cell_eq k r k' r'

/--
[jsi_cell_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_cell_mem_rect_eq
  {k r α β c d : ℤ} :
-- imply
  jsi_cell k r ∈ rect α β c d ↔ α ≤ k ∧ k ≤ β ∧ c ≤ r ∧ r ≤ d := by
-- proof
  apply StatMech.Lattice.jsi_cell_mem_rect k r α β c d

/--
[jsi_vstep_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_vstep_adj_eq
  {k r : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (jsi_cell k r) (jsi_cell k (r + 1)) := by
-- proof
  apply StatMech.Lattice.jsi_vstep_adj k r

/--
[jsi_hstep_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_hstep_adj_eq
  {k k' r : ℤ}
-- given
  (h : k - k' = 1 ∨ k - k' = -1) :
-- imply
  (hypercubicLattice 2).Adj (jsi_cell k r) (jsi_cell k' r) := by
-- proof
  apply StatMech.Lattice.jsi_hstep_adj k k' r h

/--
[jsi_col_consecutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_col_consecutive_eq
  {P : Set (Site 2)}
  {m m' c d : ℤ}
  {A : JsiRowArc P m m' c d}
  {r s : ℤ}
-- given
  (hr : c ≤ r)
  (hrd : r ≤ d)
  (hs : c ≤ s)
  (hsd : s ≤ d)
  (hrs : r - s = 1 ∨ r - s = -1) :
-- imply
  -1 ≤ A.col r - A.col s ∧ A.col r - A.col s ≤ 1 := by
-- proof
  apply StatMech.Lattice.jsi_col_consecutive A r s hr hrd hs hsd hrs

/--
[jsi_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_mem_leftRegion_eq
  {col : ℤ → ℤ}
  {α β c d : ℤ}
  {z : Site 2} :
-- imply
  z ∈ jsi_leftRegion col α β c d ↔ z ∈ rect α β c d ∧ z 0 ≤ col (z 1) := by
-- proof
  apply StatMech.Lattice.jsi_mem_leftRegion col α β c d z

/--
[jsi_mem_leftRegionLt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_mem_leftRegionLt_eq
  {col : ℤ → ℤ}
  {α β c d : ℤ}
  {z : Site 2} :
-- imply
  z ∈ jsi_leftRegionLt col α β c d ↔ z ∈ rect α β c d ∧ z 0 < col (z 1) := by
-- proof
  apply StatMech.Lattice.jsi_mem_leftRegionLt col α β c d z

/--
[jsi_arcSeparatingSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_arcSeparatingSet_eq
  {P : Set (Site 2)}
  {α β m m' c d : ℤ}
  {A : JsiRowArc P m m' c d}
-- given
  (hαm : α ≤ m)
  (hm'β : m' < β) :
-- imply
  ArcSeparatingSet P α β c d := by
-- proof
  apply StatMech.Lattice.jsi_arcSeparatingSet hαm hm'β A

/--
[jsi_arcSeparatingSetLt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_arcSeparatingSetLt_eq
  {P : Set (Site 2)}
  {α β m m' c d : ℤ}
  {A : JsiRowArc P m m' c d}
-- given
  (hαm : α < m)
  (hm'β : m' ≤ β) :
-- imply
  ArcSeparatingSet P α β c d := by
-- proof
  apply StatMech.Lattice.jsi_arcSeparatingSetLt hαm hm'β A

/--
[jsi_hconn_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_hconn_support_eq
  {k k' r : ℤ}
  (h)
  {z : Site 2}
-- given
  (hz : z ∈ (jsi_hconn k k' r h).support) :
-- imply
  z = jsi_cell k r ∨ z = jsi_cell k' r := by
-- proof
  apply StatMech.Lattice.jsi_hconn_support k k' r z hz

/--
[jsi_arcWalk_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_arcWalk_zero_eq
  {col : ℤ → ℤ}
  (hsh)
  {c : ℤ} :
-- imply
  jsi_arcWalk col hsh c 0 = (SimpleGraph.Walk.nil).copy rfl (by rw [jsi_cell_eq]; norm_num) := by
-- proof
  apply StatMech.Lattice.jsi_arcWalk_zero col c

/--
[jsi_arcWalk_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_arcWalk_succ_eq
  {col : ℤ → ℤ}
  (hsh)
  {c : ℤ}
  {n : ℕ} :
-- imply
  jsi_arcWalk col hsh c (n + 1) = (((jsi_arcWalk col hsh c n).append (SimpleGraph.Walk.cons (jsi_vstep_adj (col (c + (n : ℤ))) (c + (n : ℤ))) (jsi_hconn (col (c + (n : ℤ))) (col (c + (n : ℤ) + 1)) (c + (n : ℤ) + 1) (by have := hsh (c + (n : ℤ)); omega)))).copy rfl (by have heq : c + (n : ℤ) + 1 = c + ((n + 1 : ℕ) : ℤ) := by push_cast; ring rw [jsi_cell_eq]; exact ⟨by rw [heq], heq⟩)) := by
-- proof
  apply StatMech.Lattice.jsi_arcWalk_succ col c n

/--
[jsi_arcWalk_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_arcWalk_support_subset_eq
  {P : Set (Site 2)}
  {col : ℤ → ℤ}
  (hsh)
  {c : ℤ} :
-- imply
  (n : ℕ) → (hP : ∀ j : ℕ, j ≤ n → jsi_cell (col (c + j)) (c + j) ∈ P) → (hPc : ∀ j : ℕ, j < n → jsi_cell (col (c + j)) (c + j + 1) ∈ P) → (z : Site 2) → z ∈ (jsi_arcWalk col hsh c n).support → z ∈ P := by
-- proof
  apply StatMech.Lattice.jsi_arcWalk_support_subset P col c

/--
[jsi_monotoneArc_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_monotoneArc_walk_eq
  {P : Set (Site 2)}
  {m m' c d : ℤ}
  {A : JsiMonotoneArc P m m' c d} :
-- imply
  ∃ (n : ℕ) (W : (hypercubicLattice 2).Walk (jsi_cell (A.col c) c) (jsi_cell (A.col (c + n)) (c + n))), c + (n : ℤ) = d ∧ (∀ z ∈ W.support, z ∈ P) := by
-- proof
  apply StatMech.Lattice.jsi_monotoneArc_walk A

/--
[jsi_separatingSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_separatingSide_eq
  {P : Set (Site 2)}
  {α β m m' c d : ℤ}
  {A : JsiRowArc P m m' c d}
-- given
  (hαm : α ≤ m)
  (hm'β : m' < β) :
-- imply
  ArcSeparatingSet P α β c d := by
-- proof
  apply StatMech.Lattice.jsi_separatingSide hαm hm'β A

/--
[jsi_separatingSideLt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_separatingSideLt_eq
  {P : Set (Site 2)}
  {α β m m' c d : ℤ}
  {A : JsiRowArc P m m' c d}
-- given
  (hαm : α < m)
  (hm'β : m' ≤ β) :
-- imply
  ArcSeparatingSet P α β c d := by
-- proof
  apply StatMech.Lattice.jsi_separatingSideLt hαm hm'β A

/--
[jsi_arc_sides_of_hasMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_arc_sides_of_hasMonotone_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
-- given
  (hαm : α ≤ m)
  (hm'β : m' < β)
  (h : JsiHasMonotoneArc ω m m' c d) :
-- imply
  StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
-- proof
  apply StatMech.Lattice.jsi_arc_sides_of_hasMonotone ω hαm hm'β h

/--
[jsi_arc_sides_of_rowArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_arc_sides_of_rowArc_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {α β m m' c d : ℤ}
-- given
  (hαm : α ≤ m)
  (hm'β : m' < β)
  (A : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d), JsiRowArc (overlapComp ω m m' c d xB hxB) m m' c d) :
-- imply
  StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
-- proof
  apply StatMech.Lattice.jsi_arc_sides_of_rowArc ω hαm hm'β A

/--
[jsi_rsw_strip_glue_of_rowArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanStripInduction.lean)
-/
@[path]
private lemma jsi_rsw_strip_glue_of_rowArc_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a m m' b c d : ℤ}
-- given
  (hpa : PositivelyAssociated μ)
  (ham : a < m)
  (hmm' : m ≤ m')
  (hm'b : m' < b)
  (AL : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d), JsiRowArc (overlapComp ω m m' c d xB hxB) m m' c d)
  (AR : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d), JsiRowArc (overlapComp ω m m' c d xB hxB) m m' c d) :
-- imply
  μ.real (horizontalCrossingEvent a m' c d) * μ.real (verticalCrossingEvent m m' c d) * μ.real (horizontalCrossingEvent m b c d) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Lattice.jsi_rsw_strip_glue_of_rowArc μ hpa ham hmm' hm'b AL AR


-- created on 2026-10-23
