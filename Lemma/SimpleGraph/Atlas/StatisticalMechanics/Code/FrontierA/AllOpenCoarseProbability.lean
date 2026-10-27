import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbability.Part2
open Finset Set SimpleGraph MeasureTheory Filter Topology StatMech StatMech.FrontierA


/--
[measurableSet_bgF2IndexAllOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma measurableSet_bgF2IndexAllOpen_eq
  {L : ℕ}
  {j : Site 2} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 (Site 2)) | bgf2_IndexAllOpen omega L j} := by
-- proof
  apply StatMech.FrontierA.measurableSet_bgF2IndexAllOpen L j

/--
[measurableSet_faithfulAllOpenTrifAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma measurableSet_faithfulAllOpenTrifAt_eq
  {L : ℕ}
  {j : Site 2} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 (Site 2)) | FaithfulAllOpenTrifAt omega L j} := by
-- proof
  apply StatMech.FrontierA.measurableSet_faithfulAllOpenTrifAt L j

/--
[bgf2_indexAllOpen_shift_centre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma bgf2_indexAllOpen_shift_centre_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j : Site 2} :
-- imply
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd (bgf2_centre L j) bgf2_IndexAllOpen (shift g omega) L j ↔ bgf2_IndexAllOpen omega L 0 := by
-- proof
  apply StatMech.FrontierA.bgf2_indexAllOpen_shift_centre omega L j

/--
[faithfulAllOpenTrifAt_shift_centre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma faithfulAllOpenTrifAt_shift_centre_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {j : Site 2} :
-- imply
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd (bgf2_centre L j) FaithfulAllOpenTrifAt (shift g omega) L j ↔ FaithfulAllOpenTrifAt omega L 0 := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpenTrifAt_shift_centre omega L j

/--
[faithfulAllOpenTrifAt_prob_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma faithfulAllOpenTrifAt_prob_const_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  {L : ℕ}
  {j : Site 2}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu) :
-- imply
  mu {omega | FaithfulAllOpenTrifAt omega L j} = mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpenTrifAt_prob_const mu hinv L j

/--
[faithfulAllOpenTrifIndicesInBox_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma faithfulAllOpenTrifIndicesInBox_eq_sum_indicator_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L N : ℕ} :
-- imply
  ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) = ∑ j ∈ boxFinsetBK 2 N, ({omega' | FaithfulAllOpenTrifAt omega' L j}.indicator (fun _ => (1 : ℝ≥0∞))) omega := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpenTrifIndicesInBox_eq_sum_indicator omega L N

/--
[expected_faithfulAllOpenTrifIndicesInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma expected_faithfulAllOpenTrifIndicesInBox_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  {L N : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu) :
-- imply
  ∫⁻ omega, ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu = (boxFinsetBK 2 N).card • mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
-- proof
  apply StatMech.FrontierA.expected_faithfulAllOpenTrifIndicesInBox mu hinv L N

/--
[faithfulAllOpenTrifIndicesInBox_count_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma faithfulAllOpenTrifIndicesInBox_count_bound_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {L N : ℕ} :
-- imply
  (faithfulAllOpenTrifIndicesInBox omega L N).card ≤ faithfulAllOpenBoundaryCard L N := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpenTrifIndicesInBox_count_bound omega L N

/--
[boxSV_boundaryCard_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma boxSV_boundaryCard_two_eq
  {r : ℕ}
-- given
  (hr : 1 ≤ r) :
-- imply
  (boxSV_boundaryCard 2 r : ℝ) = 8 * r := by
-- proof
  apply StatMech.FrontierA.boxSV_boundaryCard_two r hr

/--
[boxFinsetBK_card_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma boxFinsetBK_card_two_eq
  {N : ℕ} :
-- imply
  ((boxFinsetBK 2 N).card : ℝ) = (2 * (N : ℝ) + 1) ^ 2 := by
-- proof
  apply StatMech.FrontierA.boxFinsetBK_card_two N

/--
[faithfulAllOpen_boundary_volume_ratio_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma faithfulAllOpen_boundary_volume_ratio_le_eq
  {L N : ℕ}
-- given
  (hN : 1 ≤ N) :
-- imply
  (faithfulAllOpenBoundaryCard L N : ℝ) / ((boxFinsetBK 2 N).card : ℝ) ≤ (8 * (3 * L + 2) : ℝ) / N := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpen_boundary_volume_ratio_le L N hN

/--
[faithfulAllOpen_boundary_volume_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma faithfulAllOpen_boundary_volume_tendsto_eq
  {L : ℕ} :
-- imply
  Tendsto (fun N => (faithfulAllOpenBoundaryCard L N : ℝ) / ((boxFinsetBK 2 N).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpen_boundary_volume_tendsto L

/--
[faithfulAllOpenTrifAt_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean)
-/
@[path]
private lemma faithfulAllOpenTrifAt_prob_eq_zero_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure mu]
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu) :
-- imply
  mu {omega | FaithfulAllOpenTrifAt omega L 0} = 0 := by
-- proof
  apply StatMech.FrontierA.faithfulAllOpenTrifAt_prob_eq_zero mu hinv L


-- created on 2026-10-23
