import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbabilityGeneral.Part2
open Finset Set SimpleGraph MeasureTheory Filter Topology StatMech StatMech.FrontierA


/--
[measurableSet_bgfdIndexAllOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma measurableSet_bgfdIndexAllOpen_eq
  {d : ℕ}
  {L : ℕ}
  {j : Site d} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 (Site d)) | BgfdIndexAllOpen omega L j} := by
-- proof
  apply StatMech.FrontierA.measurableSet_bgfdIndexAllOpen L j

/--
[measurableSet_bgfdFaithfulAllOpenTrifAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma measurableSet_bgfdFaithfulAllOpenTrifAt_eq
  {d : ℕ}
  {L : ℕ}
  {j : Site d} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 (Site d)) | BgfdFaithfulAllOpenTrifAt omega L j} := by
-- proof
  apply StatMech.FrontierA.measurableSet_bgfdFaithfulAllOpenTrifAt L j

/--
[bgfd_indexAllOpen_shift_centre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma bgfd_indexAllOpen_shift_centre_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j : Site d} :
-- imply
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (bgfdCentre L j) BgfdIndexAllOpen (shift g omega) L j ↔ BgfdIndexAllOpen omega L 0 := by
-- proof
  apply StatMech.FrontierA.bgfd_indexAllOpen_shift_centre omega L j

/--
[bgfdFaithfulAllOpenTrifAt_shift_centre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpenTrifAt_shift_centre_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {j : Site d} :
-- imply
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (bgfdCentre L j) BgfdFaithfulAllOpenTrifAt (shift g omega) L j ↔ BgfdFaithfulAllOpenTrifAt omega L 0 := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpenTrifAt_shift_centre omega L j

/--
[bgfdFaithfulAllOpenTrifAt_prob_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpenTrifAt_prob_const_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
  {j : Site d}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  mu {omega | BgfdFaithfulAllOpenTrifAt omega L j} = mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpenTrifAt_prob_const mu hinv L j

/--
[bgfdFaithfulAllOpenTrifIndicesInBox_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpenTrifIndicesInBox_eq_sum_indicator_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L N : ℕ} :
-- imply
  ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) = ∑ j ∈ boxFinsetBK d N, ({omega' | BgfdFaithfulAllOpenTrifAt omega' L j}.indicator (fun _ => (1 : ℝ≥0∞))) omega := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpenTrifIndicesInBox_eq_sum_indicator omega L N

/--
[expected_bgfdFaithfulAllOpenTrifIndicesInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma expected_bgfdFaithfulAllOpenTrifIndicesInBox_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  {L N : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  ∫⁻ omega, ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu = (boxFinsetBK d N).card • mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
-- proof
  apply StatMech.FrontierA.expected_bgfdFaithfulAllOpenTrifIndicesInBox mu hinv L N

/--
[bgfdFaithfulAllOpenTrifIndicesInBox_count_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpenTrifIndicesInBox_count_bound_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {L N : ℕ} :
-- imply
  (bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card ≤ bgfdFaithfulAllOpenBoundaryCard d L N := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpenTrifIndicesInBox_count_bound omega L N

/--
[bgfd_boxFinsetBK_card_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma bgfd_boxFinsetBK_card_real_eq
  {d : ℕ}
  {d N : ℕ} :
-- imply
  ((boxFinsetBK d N).card : ℝ) = (2 * (N : ℝ) + 1) ^ d := by
-- proof
  apply StatMech.FrontierA.bgfd_boxFinsetBK_card_real d N

/--
[bgfdFaithfulAllOpen_boundary_volume_ratio_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpen_boundary_volume_ratio_le_eq
  {d : ℕ}
  {d L N : ℕ}
-- given
  (hd : 1 ≤ d)
  (hN : 1 ≤ N) :
-- imply
  (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) / ((boxFinsetBK d N).card : ℝ) ≤ (2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d) / N := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpen_boundary_volume_ratio_le d L N hd hN

/--
[bgfdFaithfulAllOpen_boundary_volume_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpen_boundary_volume_tendsto_eq
  {d : ℕ}
  {d L : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun N => (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) / ((boxFinsetBK d N).card : ℝ)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpen_boundary_volume_tendsto d L hd

/--
[bgfdFaithfulAllOpenTrifAt_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean)
-/
@[path]
private lemma bgfdFaithfulAllOpenTrifAt_prob_eq_zero_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure mu]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} = 0 := by
-- proof
  apply StatMech.FrontierA.bgfdFaithfulAllOpenTrifAt_prob_eq_zero mu hd hinv L


-- created on 2026-10-23
