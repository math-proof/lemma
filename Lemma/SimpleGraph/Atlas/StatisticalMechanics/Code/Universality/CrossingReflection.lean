import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[crf_swap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_swap_zero_eq
  {x : Site 2} :
-- imply
  (crf_swap x) 0 = x 1 := by
-- proof
  apply StatMech.Universality.crf_swap_zero x

/--
[crf_swap_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_swap_one_eq
  {x : Site 2} :
-- imply
  (crf_swap x) 1 = x 0 := by
-- proof
  apply StatMech.Universality.crf_swap_one x

/--
[crf_swap_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_swap_symm_eq :
-- imply
  crf_swap.symm = crf_swap := by
-- proof
  apply StatMech.Universality.crf_swap_symm

/--
[crf_swap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_swap_involutive_eq
  {x : Site 2} :
-- imply
  crf_swap (crf_swap x) = x := by
-- proof
  apply StatMech.Universality.crf_swap_involutive x

/--
[crf_adj_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_adj_swap_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (crf_swap x) (crf_swap y) := by
-- proof
  apply StatMech.Universality.crf_adj_swap x y

/--
[crf_edgeEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_edgeEquiv_symm_apply_eq
  {e : Sym2 (Site 2)} :
-- imply
  crf_edgeEquiv.symm e = e.map crf_swap := by
-- proof
  apply StatMech.Universality.crf_edgeEquiv_symm_apply e

/--
[crf_swapConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_swapConfig_apply_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  crf_swapConfig ω e = ω (e.map crf_swap) := by
-- proof
  apply StatMech.Universality.crf_swapConfig_apply ω e

/--
[crf_measurable_swapConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_measurable_swapConfig_eq :
-- imply
  Measurable crf_swapConfig := by
-- proof
  apply StatMech.Universality.crf_measurable_swapConfig

/--
[crf_map_swapConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_map_swapConfig_eq :
-- imply
  Measure.map crf_swapConfig rba_selfDualMeasure = rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.crf_map_swapConfig

/--
[crf_swap_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_swap_invariant_eq :
-- imply
  MeasurePreserving crf_swapConfig rba_selfDualMeasure rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.crf_swap_invariant

/--
[crf_isOpenEdge_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_isOpenEdge_swap_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2} :
-- imply
  IsOpenEdge 2 (crf_swapConfig ω) x y ↔ IsOpenEdge 2 ω (crf_swap x) (crf_swap y) := by
-- proof
  apply StatMech.Universality.crf_isOpenEdge_swap ω x y

/--
[crf_mem_rect_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_mem_rect_swap_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rect a b c d ↔ (crf_swap x) ∈ rect c d a b := by
-- proof
  apply StatMech.Universality.crf_mem_rect_swap a b c d x

/--
[crf_mem_bottomSide_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_mem_bottomSide_swap_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ bottomSide a b c d ↔ (crf_swap x) ∈ leftSide c d a b := by
-- proof
  apply StatMech.Universality.crf_mem_bottomSide_swap a b c d x

/--
[crf_mem_topSide_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_mem_topSide_swap_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ topSide a b c d ↔ (crf_swap x) ∈ rightSide c d a b := by
-- proof
  apply StatMech.Universality.crf_mem_topSide_swap a b c d x

/--
[crf_vertical_to_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_vertical_to_horizontal_eq
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : VerticalCrossing ω a b c d) :
-- imply
  HorizontalCrossing (crf_swapConfig ω) c d a b := by
-- proof
  apply StatMech.Universality.crf_vertical_to_horizontal a b c d ω h

/--
[crf_horizontal_to_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_horizontal_to_vertical_eq
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : HorizontalCrossing (crf_swapConfig ω) c d a b) :
-- imply
  VerticalCrossing ω a b c d := by
-- proof
  apply StatMech.Universality.crf_horizontal_to_vertical a b c d ω h

/--
[crf_verticalCrossingEvent_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_verticalCrossingEvent_swap_eq
  {a b c d : ℤ} :
-- imply
  verticalCrossingEvent a b c d = crf_swapConfig ⁻¹' horizontalCrossingEvent c d a b := by
-- proof
  apply StatMech.Universality.crf_verticalCrossingEvent_swap a b c d

/--
[crf_verticalCrossing_eq_horizontal_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_verticalCrossing_eq_horizontal_swap_eq
  {a b c d : ℤ}
-- given
  (hmeas : MeasurableSet (horizontalCrossingEvent c d a b)) :
-- imply
  rba_selfDualMeasure.real (verticalCrossingEvent a b c d) = rba_selfDualMeasure.real (horizontalCrossingEvent c d a b) := by
-- proof
  apply StatMech.Universality.crf_verticalCrossing_eq_horizontal_swap a b c d hmeas

/--
[crf_hrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_hrefl_eq
-- given
  (hmeas : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
-- imply
  ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n → rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) := by
-- proof
  apply StatMech.Universality.crf_hrefl hmeas

/--
[crf_hrefl_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean)
-/
@[path]
private lemma crf_hrefl_fixed_eq
  {k0 : ℕ}
-- given
  (hmeas : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
-- imply
  ∀ n : ℤ, 0 < n → rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) := by
-- proof
  apply StatMech.Universality.crf_hrefl_fixed hmeas


-- created on 2026-10-23
