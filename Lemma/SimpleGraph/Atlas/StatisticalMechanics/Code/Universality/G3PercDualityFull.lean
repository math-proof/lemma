import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
open MeasureTheory ProbabilityTheory StatMech StatMech.Universality


/--
[dualConfig_eq_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma dualConfig_eq_comp_eq :
-- imply
  (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) = (fun η e => !(η e)) ∘ (Equiv.piCongrLeft (fun _ => Bool) crossEdge) := by
-- proof
  apply StatMech.Universality.dualConfig_eq_comp

/--
[measurable_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma measurable_complement_eq :
-- imply
  Measurable (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e)) := by
-- proof
  apply StatMech.Universality.measurable_complement

/--
[measurable_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma measurable_reindex_eq :
-- imply
  Measurable (Equiv.piCongrLeft (fun _ => Bool) (crossEdge : Sym2 (Site 2) ≃ Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.measurable_reindex

/--
[map_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma map_complement_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Measure.map (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e)) (bernoulliProductMeasure p hp) = bernoulliProductMeasure (1 - p) tsub_le_self := by
-- proof
  apply StatMech.Universality.map_complement p hp

/--
[map_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma map_reindex_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Measure.map (Equiv.piCongrLeft (fun _ => Bool) crossEdge) (bernoulliProductMeasure p hp) = bernoulliProductMeasure p hp := by
-- proof
  apply StatMech.Universality.map_reindex p hp

/--
[map_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma map_dualConfig_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Measure.map dualConfig (bernoulliProductMeasure p hp) = bernoulliProductMeasure (1 - p) tsub_le_self := by
-- proof
  apply StatMech.Universality.map_dualConfig p hp

/--
[selfDual_density_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma selfDual_density_iff_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  1 - p = p ↔ p = 2⁻¹ := by
-- proof
  apply StatMech.Universality.selfDual_density_iff p hp

/--
[selfDual_density_iff_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma selfDual_density_iff_real_eq
  {p : ℝ} :
-- imply
  1 - p = p ↔ p = 1 / 2 := by
-- proof
  apply StatMech.Universality.selfDual_density_iff_real p

/--
[one_sub_half_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma one_sub_half_eq_eq :
-- imply
  (1 : ℝ≥0) - 2⁻¹ = 2⁻¹ := by
-- proof
  apply StatMech.Universality.one_sub_half_eq

/--
[bernoulliProductMeasure_selfDual_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma bernoulliProductMeasure_selfDual_half_eq :
-- imply
  Measure.map dualConfig (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one := by
-- proof
  apply StatMech.Universality.bernoulliProductMeasure_selfDual_half

/--
[selfDual_point_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma selfDual_point_unique_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (1 - p = p ↔ p = 2⁻¹) ∧ Measure.map dualConfig (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one := by
-- proof
  apply StatMech.Universality.selfDual_point_unique p hp

/--
[map_dualConfig_dualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean)
-/
@[path]
private lemma map_dualConfig_dualConfig_eq
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Measure.map dualConfig (Measure.map dualConfig (bernoulliProductMeasure p hp)) = bernoulliProductMeasure p hp := by
-- proof
  apply StatMech.Universality.map_dualConfig_dualConfig p hp


-- created on 2026-10-23
