import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
open StatMech StatMech.Exact3D StatMech.Exact3D.IsingAnalyticRGToExponentTarget StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget


/--
[eventually_mem_isingLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_isingLeftCriticalIoo_eq
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.eventually_mem_isingLeftCriticalIoo hδ

/--
[betaC_sub_pos_of_mem_isingLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_isingLeftCriticalIoo_eq
  {δ β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ

/--
[betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo_eq
  {δ β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < δ := by
-- proof
  apply StatMech.Exact3D.betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ

/--
[beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC_eq
  {δ β : ℝ}
-- given
  (hδle : δ ≤ Ising.betaC 3)
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
-- imply
  0 < β := by
-- proof
  apply StatMech.Exact3D.beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ

/--
[eventually_betaC_sub_pos_isingLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_isingLeftCriticalIoo_eq
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.eventually_betaC_sub_pos_isingLeftCriticalIoo hδ

/--
[eventually_betaC_sub_lt_delta_isingLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_isingLeftCriticalIoo_eq
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < δ := by
-- proof
  apply StatMech.Exact3D.eventually_betaC_sub_lt_delta_isingLeftCriticalIoo hδ

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.hasCorrelationLength T hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.eventually_mem_leftCriticalInterval T

/--
[betaC_sub_pos_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.betaC_sub_pos_of_mem_leftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.betaC_sub_lt_delta_of_mem_leftCriticalInterval T hβ

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_prefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_prefactor_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.prefactor β := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.eventually_prefactor_pos T

/--
[eventually_length_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_length_scaling_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = T.prefactor β * Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.eventually_length_scaling T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.rgToExponentBridge T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.hasCriticalNu T

/--
[eventually_correlationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.eventually_correlationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.correlationLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingAnalyticRGToExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.hasCorrelationLength T hβ

/--
[hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasInverseCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.mass β) := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.hasInverseCorrelationLength T hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_mem_leftCriticalInterval T

/--
[betaC_sub_pos_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.betaC_sub_pos_of_mem_leftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.betaC_sub_lt_delta_of_mem_leftCriticalInterval T hβ

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_mass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mass_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_mass_pos T

/--
[eventually_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasInverseCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.mass β) := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_hasInverseCorrelationLength T

/--
[eventually_correlationLength_eq_inv_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_inv_mass_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = (T.mass β)⁻¹ := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_correlationLength_eq_inv_mass T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_prefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_prefactor_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.prefactor β := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_prefactor_pos T

/--
[eventually_length_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_length_scaling_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = T.prefactor β * Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_length_scaling T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.rgToExponentBridge T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.hasCriticalNu T

/--
[eventually_correlationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.eventually_correlationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[congr_predictedExponent_toLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toLengthTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toLengthTarget = IsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toLengthTarget := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.congr_predictedExponent_toLengthTarget hpred T

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassAnalyticRGToExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.hasCorrelationLength T hβ

/--
[hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasInverseCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.mass β) := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.hasInverseCorrelationLength T hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_mem_leftCriticalInterval T

/--
[betaC_sub_pos_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_leftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.betaC_sub_pos_of_mem_leftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_leftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.betaC_sub_lt_delta_of_mem_leftCriticalInterval T hβ

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_mass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mass_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_mass_pos T

/--
[eventually_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasInverseCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.mass β) := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_hasInverseCorrelationLength T

/--
[eventually_correlationLength_eq_inv_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_inv_mass_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = (T.mass β)⁻¹ := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_correlationLength_eq_inv_mass T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_massPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_massPrefactor_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.massPrefactor β := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_massPrefactor_pos T

/--
[eventually_mass_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mass_scaling_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.mass β = T.massPrefactor β * Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_mass_scaling T

/--
[lengthScalingFromMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma lengthScalingFromMass_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  T.correlationLength β = (T.massPrefactor β)⁻¹ * Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.lengthScalingFromMass T hβ

/--
[toMassTarget_toLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toMassTarget_toLengthTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  T.toMassTarget.toLengthTarget = T.toLengthTarget := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.toMassTarget_toLengthTarget T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.rgToExponentBridge T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.hasCriticalNu T

/--
[eventually_correlationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_liminfCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.eventually_correlationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[congr_predictedExponent_toMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toMassTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toMassTarget = IsingMassAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toMassTarget := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.congr_predictedExponent_toMassTarget hpred T

/--
[congr_predictedExponent_toLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toLengthTarget_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toLengthTarget = IsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toLengthTarget := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.congr_predictedExponent_toLengthTarget hpred T

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_3
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_3
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_3
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassPowerLawAnalyticRGToExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[free_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma free_hasCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.free_hasCorrelationLength T hβ

/--
[plus_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma plus_hasCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.plus_hasCorrelationLength T hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.eventually_mem_leftCriticalInterval T

/--
[betaC_sub_pos_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_leftCriticalInterval_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.betaC_sub_pos_of_mem_leftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_leftCriticalInterval_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.betaC_sub_lt_delta_of_mem_leftCriticalInterval T hβ

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_free_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_free_hasCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.eventually_free_hasCorrelationLength T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_prefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_prefactor_pos_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.prefactor β := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.eventually_prefactor_pos T

/--
[eventually_length_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_length_scaling_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = T.prefactor β * Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.eventually_length_scaling T

/--
[toPlusLengthTarget_correlationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toPlusLengthTarget_correlationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  T.toPlusLengthTarget.correlationLength = T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.toPlusLengthTarget_correlationLength T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  C.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.rgToExponentBridge T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.hasCriticalNu T

/--
[eventually_correlationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_liminfCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.eventually_correlationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[congr_predictedExponent_toPlusLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toPlusLengthTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toPlusLengthTarget = IsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toPlusLengthTarget := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.congr_predictedExponent_toPlusLengthTarget hpred T

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_4
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_4
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_4
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeAnalyticRGToPlusExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[plus_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.freeMass β) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.plus_hasInverseCorrelationLength T hβ

/--
[free_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma free_hasCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.free_hasCorrelationLength T hβ

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.hasCorrelationLength T hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_mem_leftCriticalInterval T

/--
[betaC_sub_pos_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_leftCriticalInterval_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.betaC_sub_pos_of_mem_leftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_leftCriticalInterval_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.betaC_sub_lt_delta_of_mem_leftCriticalInterval T hβ

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_freeMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_freeMass_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.freeMass β := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_freeMass_pos T

/--
[eventually_free_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_free_hasInverseCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (T.freeMass β) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_free_hasInverseCorrelationLength T

/--
[eventually_plus_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_plus_hasInverseCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.freeMass β) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_plus_hasInverseCorrelationLength T

/--
[eventually_free_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_free_hasCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_free_hasCorrelationLength T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_correlationLength_eq_inv_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_inv_mass_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = (T.freeMass β)⁻¹ := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_correlationLength_eq_inv_mass T

/--
[eventually_prefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_prefactor_pos_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.prefactor β := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_prefactor_pos T

/--
[eventually_length_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_length_scaling_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = T.prefactor β * Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_length_scaling T

/--
[toPlusMassTarget_toLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toPlusMassTarget_toLengthTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  T.toPlusMassTarget.toLengthTarget = T.toPlusLengthTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.toPlusMassTarget_toLengthTarget T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  C.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.rgToExponentBridge T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.hasCriticalNu T

/--
[eventually_correlationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_liminfCorrelationLength_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.eventually_correlationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[congr_predictedExponent_toFreeLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toFreeLengthTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toFreeLengthTarget = FreeAnalyticRGToPlusExponentTarget.congr_predictedExponent hpred T.toFreeLengthTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.congr_predictedExponent_toFreeLengthTarget hpred T

/--
[congr_predictedExponent_toPlusMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toPlusMassTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toPlusMassTarget = IsingMassAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toPlusMassTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.congr_predictedExponent_toPlusMassTarget hpred T

/--
[congr_predictedExponent_toPlusLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toPlusLengthTarget_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toPlusLengthTarget = IsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toPlusLengthTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.congr_predictedExponent_toPlusLengthTarget hpred T

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_5
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_5
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_5
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeMassAnalyticRGToPlusExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[plus_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma plus_hasInverseCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.freeMass β) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.plus_hasInverseCorrelationLength T hβ

/--
[free_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma free_hasCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.free_hasCorrelationLength T hβ

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCorrelationLength_eq_5
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.hasCorrelationLength T hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_mem_leftCriticalInterval T

/--
[betaC_sub_pos_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_leftCriticalInterval_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.betaC_sub_pos_of_mem_leftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_leftCriticalInterval_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.betaC_sub_lt_delta_of_mem_leftCriticalInterval T hβ

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_freeMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_freeMass_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.freeMass β := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_freeMass_pos T

/--
[eventually_free_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_free_hasInverseCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (T.freeMass β) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_free_hasInverseCorrelationLength T

/--
[eventually_plus_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_plus_hasInverseCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.freeMass β) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_plus_hasInverseCorrelationLength T

/--
[eventually_free_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_free_hasCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_free_hasCorrelationLength T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_correlationLength_eq_inv_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_inv_mass_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = (T.freeMass β)⁻¹ := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_correlationLength_eq_inv_mass T

/--
[eventually_massPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_massPrefactor_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.massPrefactor β := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_massPrefactor_pos T

/--
[eventually_freeMass_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_freeMass_scaling_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.freeMass β = T.massPrefactor β * Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_freeMass_scaling T

/--
[lengthScalingFromFreeMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma lengthScalingFromFreeMass_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  T.correlationLength β = (T.massPrefactor β)⁻¹ * Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.lengthScalingFromFreeMass T hβ

/--
[eventually_lengthScalingFromFreeMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_lengthScalingFromFreeMass_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = (T.massPrefactor β)⁻¹ * Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_lengthScalingFromFreeMass T

/--
[toFreeMassTarget_toFreeLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toFreeMassTarget_toFreeLengthTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  T.toFreeMassTarget.toFreeLengthTarget = T.toFreeLengthTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.toFreeMassTarget_toFreeLengthTarget T

/--
[toFreeMassTarget_toPlusMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toFreeMassTarget_toPlusMassTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  T.toFreeMassTarget.toPlusMassTarget = T.toPlusMassTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.toFreeMassTarget_toPlusMassTarget T

/--
[toPlusMassTarget_toLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toPlusMassTarget_toLengthTarget_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  T.toPlusMassTarget.toLengthTarget = T.toPlusLengthTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.toPlusMassTarget_toLengthTarget T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.rgToExponentBridge T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.hasCriticalNu T

/--
[eventually_correlationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_liminfCorrelationLength_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.correlationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.eventually_correlationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq_6
  {C : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[congr_predictedExponent_toFreeMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toFreeMassTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toFreeMassTarget = FreeMassAnalyticRGToPlusExponentTarget.congr_predictedExponent hpred T.toFreeMassTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.congr_predictedExponent_toFreeMassTarget hpred T

/--
[congr_predictedExponent_toFreeLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toFreeLengthTarget_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toFreeLengthTarget = FreeAnalyticRGToPlusExponentTarget.congr_predictedExponent hpred T.toFreeLengthTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.congr_predictedExponent_toFreeLengthTarget hpred T

/--
[congr_predictedExponent_toPlusMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toPlusMassTarget_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toPlusMassTarget = IsingMassAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toPlusMassTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.congr_predictedExponent_toPlusMassTarget hpred T

/--
[congr_predictedExponent_toPlusLengthTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toPlusLengthTarget_eq_3
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toPlusLengthTarget = IsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toPlusLengthTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.congr_predictedExponent_toPlusLengthTarget hpred T

/--
[congr_predictedExponent_toPlusMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toPlusMassPowerLawTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toPlusMassPowerLawTarget = IsingMassPowerLawAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toPlusMassPowerLawTarget := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.congr_predictedExponent_toPlusMassPowerLawTarget hpred T

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_6
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_6
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_6
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FreeMassPowerLawToPlusAnalyticRGToExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit


-- created on 2026-10-23
