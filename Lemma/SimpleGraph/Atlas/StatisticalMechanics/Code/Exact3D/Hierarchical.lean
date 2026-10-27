import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.Hierarchical.Part4
open StatMech StatMech.Exact3D


/--
[hierarchical_thermal_gt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchical_thermal_gt_one_eq :
-- imply
  1 < hierarchicalThermalEigenvalue := by
-- proof
  apply StatMech.Exact3D.hierarchical_thermal_gt_one

/--
[hierarchical_stable_abs_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchical_stable_abs_lt_one_eq :
-- imply
  |hierarchicalStableEigenvalue| < 1 := by
-- proof
  apply StatMech.Exact3D.hierarchical_stable_abs_lt_one

/--
[hierarchicalLinearization_mem_intervals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchicalLinearization_mem_intervals_eq :
-- imply
  RatInterval.MatrixMem hierarchicalLinearization hierarchicalLinearizationIntervals := by
-- proof
  apply StatMech.Exact3D.hierarchicalLinearization_mem_intervals

/--
[hierarchicalStableLinearization_mem_intervals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchicalStableLinearization_mem_intervals_eq :
-- imply
  RatInterval.MatrixMem hierarchicalStableLinearization hierarchicalStableLinearizationIntervals := by
-- proof
  apply StatMech.Exact3D.hierarchicalStableLinearization_mem_intervals

/--
[hierarchicalStableLinearization_apply_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchicalStableLinearization_apply_bound_eq
  {x : Fin 1 → ℝ}
  {i : Fin 1} :
-- imply
  |RatInterval.matVec hierarchicalStableLinearization x i| ≤ ((1 / 2 : ℚ) : ℝ) * RatInterval.supNormVec x := by
-- proof
  apply StatMech.Exact3D.hierarchicalStableLinearization_apply_bound x i

/--
[hierarchicalFiniteSplitting_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchicalFiniteSplitting_predictedExponent_eq_eq :
-- imply
  hierarchicalFiniteSplittingCertificate.predictedExponent = hierarchicalNu := by
-- proof
  apply StatMech.Exact3D.hierarchicalFiniteSplitting_predictedExponent_eq

/--
[hierarchicalFiniteSplitting_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchicalFiniteSplitting_fixedPointEnclosure_eq :
-- imply
  hierarchicalFiniteSplittingCertificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.hierarchicalFiniteSplitting_fixedPointEnclosure

/--
[hierarchical_logSlope_eq_nu_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchical_logSlope_eq_nu_of_mem_eq
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (-1) 0) :
-- imply
  logSlope HierarchicalModel hierarchicalCorrelationLength β = hierarchicalNu := by
-- proof
  apply StatMech.Exact3D.hierarchical_logSlope_eq_nu_of_mem hβ

/--
[hierarchical_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchical_hasCriticalNu_eq :
-- imply
  HasCriticalNu HierarchicalModel hierarchicalCorrelationLength hierarchicalNu := by
-- proof
  apply StatMech.Exact3D.hierarchical_hasCriticalNu

/--
[hierarchical_bridge_via_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchical_bridge_via_exact_power_eq :
-- imply
  hierarchicalCertificate.RGToExponentBridge hierarchicalCorrelationLength := by
-- proof
  apply StatMech.Exact3D.hierarchical_bridge_via_exact_power

/--
[hierarchicalFiniteSplitting_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchicalFiniteSplitting_bridge_eq :
-- imply
  hierarchicalFiniteSplittingCertificate.RGToExponentBridge hierarchicalCorrelationLength := by
-- proof
  apply StatMech.Exact3D.hierarchicalFiniteSplitting_bridge

/--
[hierarchicalFiniteSplittingCertificate_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchicalFiniteSplittingCertificate_valid_eq :
-- imply
  hierarchicalFiniteSplittingCertificate.Valid hierarchicalCorrelationLength := by
-- proof
  apply StatMech.Exact3D.hierarchicalFiniteSplittingCertificate_valid

/--
[hierarchicalCertificate_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchicalCertificate_valid_eq :
-- imply
  hierarchicalCertificate.Valid hierarchicalCorrelationLength := by
-- proof
  apply StatMech.Exact3D.hierarchicalCertificate_valid

/--
[hierarchical_hasCriticalNu_eq_log_scale_div_log_thermal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean)
-/
@[path]
private lemma hierarchical_hasCriticalNu_eq_log_scale_div_log_thermal_eq :
-- imply
  HasCriticalNu HierarchicalModel hierarchicalCorrelationLength (Real.log hierarchicalCertificate.scale.toReal / Real.log hierarchicalCertificate.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.hierarchical_hasCriticalNu_eq_log_scale_div_log_thermal


-- created on 2026-10-23
