import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget
open StatMech StatMech.Exact3D StatMech.Exact3D.RGCertificate StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget StatMech.Exact3D.FKMassAnalyticRGToExponentTarget StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget


/--
[eventually_mem_fkBetaLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_fkBetaLeftCriticalIoo_eq
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.eventually_mem_fkBetaLeftCriticalIoo hδ

/--
[betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo_eq
  {δ β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.betaC_sub_pos_of_mem_fkBetaLeftCriticalIoo hβ

/--
[betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo_eq
  {δ β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < δ := by
-- proof
  apply StatMech.Exact3D.betaC_sub_lt_delta_of_mem_fkBetaLeftCriticalIoo hβ

/--
[beta_pos_of_mem_fkBetaLeftCriticalIoo_of_delta_le_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma beta_pos_of_mem_fkBetaLeftCriticalIoo_of_delta_le_betaC_eq
  {δ β : ℝ}
-- given
  (hδle : δ ≤ Ising.betaC 3)
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
-- imply
  0 < β := by
-- proof
  apply StatMech.Exact3D.beta_pos_of_mem_fkBetaLeftCriticalIoo_of_delta_le_betaC hδle hβ

/--
[eventually_betaC_sub_pos_fkBetaLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_fkBetaLeftCriticalIoo_eq
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.eventually_betaC_sub_pos_fkBetaLeftCriticalIoo hδ

/--
[eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo_eq
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < δ := by
-- proof
  apply StatMech.Exact3D.eventually_betaC_sub_lt_delta_fkBetaLeftCriticalIoo hδ

/--
[eventually_mem_fkPLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_fkPLeftCriticalIoo_eq
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ) :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) := by
-- proof
  apply StatMech.Exact3D.eventually_mem_fkPLeftCriticalIoo hpδ

/--
[eventually_pOfBeta_mem_fkPLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pOfBeta_mem_fkPLeftCriticalIoo_eq
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ) :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), IsingFK.pOfBeta β ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) := by
-- proof
  apply StatMech.Exact3D.eventually_pOfBeta_mem_fkPLeftCriticalIoo hpδ

/--
[pCritical_sub_pos_of_mem_fkPLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma pCritical_sub_pos_of_mem_fkPLeftCriticalIoo_eq
  {pδ p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3))) :
-- imply
  0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
-- proof
  apply StatMech.Exact3D.pCritical_sub_pos_of_mem_fkPLeftCriticalIoo hp

/--
[pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo_eq
  {pδ p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3))) :
-- imply
  IsingFK.pOfBeta (Ising.betaC 3) - p < pδ := by
-- proof
  apply StatMech.Exact3D.pCritical_sub_lt_delta_of_mem_fkPLeftCriticalIoo hp

/--
[eventually_pCritical_sub_pos_fkPLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pCritical_sub_pos_fkPLeftCriticalIoo_eq
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ) :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), 0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
-- proof
  apply StatMech.Exact3D.eventually_pCritical_sub_pos_fkPLeftCriticalIoo hpδ

/--
[eventually_pCritical_sub_lt_delta_fkPLeftCriticalIoo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pCritical_sub_lt_delta_fkPLeftCriticalIoo_eq
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ) :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), IsingFK.pOfBeta (Ising.betaC 3) - p < pδ := by
-- proof
  apply StatMech.Exact3D.eventually_pCritical_sub_lt_delta_fkPLeftCriticalIoo hpδ

/--
[hasCriticalNu_comp_pOfBeta_congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_comp_pOfBeta_congr_eventually_eq
  {βc ν : ℝ}
  {fkCorrelationLength comparisonLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta βc)) fkCorrelationLength ν)
  (hEq : ∀ᶠ β in nhdsWithin βc (Set.Iio βc), comparisonLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu (ParameterModel βc) comparisonLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_comp_pOfBeta_congr_eventually hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_eventually_eq_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength C.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  C.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq C hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : (C.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  C.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq C hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : (D.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  C.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_fk_pOfBeta_retargetBridge_congr_predictedExponent C hpred hfk hEq

/--
[valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : (C.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq C hfk hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_fk_pOfBeta_retargetBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_retargetBridge_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : (D.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_fk_pOfBeta_retargetBridge_congr_predictedExponent C hpred hfk hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_eventually_eq_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength C.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_fk_pOfBeta_eventually_eq C hfk hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_eventually_eq_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength C.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_fk_pOfBeta_eventually_eq C hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  C.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent C hpred hfk hEq

/--
[valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent C hpred hfk hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent C hpred hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : (C.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq C hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_retargetBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_retargetBridge_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hfk : (D.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_fk_pOfBeta_retargetBridge_congr_predictedExponent C hpred hfk hEq

/--
[rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  C.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo C isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[valid_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_fk_exact_power_variable_prefactor_on_Ioo C isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ hpref_pos hlogpref hscaling hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo C isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  C.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent C isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent C isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ hpref_pos hlogpref hscaling hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent C isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  C.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo C isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo C isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {C : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo C isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  C.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent C isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent C isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent C isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.isingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.hasCorrelationLength T hβ

/--
[eventually_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_betaLeftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.eventually_mem_betaLeftCriticalInterval T

/--
[betaC_sub_pos_of_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_betaLeftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.betaC_sub_pos_of_mem_betaLeftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval T hβ

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.δ := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.isingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_ising_fk_length_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_ising_fk_length_agree_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.isingCorrelationLength β = T.fkCorrelationLength (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.eventually_ising_fk_length_agree T

/--
[hasCriticalNu_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_comp_pOfBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu (ParameterModel (Ising.betaC 3)) (fun β => T.fkCorrelationLength (IsingFK.pOfBeta β)) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.hasCriticalNu_comp_pOfBeta T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.hasCriticalNu T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.rgToExponentBridge T

/--
[eventually_isingCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_isingCorrelationLength_eq_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.isingCorrelationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.eventually_isingCorrelationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.isingCorrelationLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
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
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKToIsingAnalyticRGToExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.isingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.hasCorrelationLength T hβ

/--
[eventually_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_betaLeftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_mem_betaLeftCriticalInterval T

/--
[eventually_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_pLeftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3)) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_mem_pLeftCriticalInterval T

/--
[eventually_pOfBeta_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pOfBeta_mem_pLeftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), IsingFK.pOfBeta β ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3)) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_pOfBeta_mem_pLeftCriticalInterval T

/--
[betaC_sub_pos_of_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_betaLeftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.betaC_sub_pos_of_mem_betaLeftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.betaδ := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval T hβ

/--
[pCritical_sub_pos_of_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma pCritical_sub_pos_of_mem_pLeftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3))) :
-- imply
  0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.pCritical_sub_pos_of_mem_pLeftCriticalInterval T hp

/--
[pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3))) :
-- imply
  IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval T hp

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.betaδ := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_pCritical_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pCritical_sub_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), 0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_pCritical_sub_pos T

/--
[eventually_pCritical_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pCritical_sub_lt_delta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_pCritical_sub_lt_delta T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.isingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_fkPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkPrefactor_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), 0 < T.fkPrefactor p := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_fkPrefactor_pos T

/--
[eventually_fkPrefactor_pos_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkPrefactor_pos_comp_pOfBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.fkPrefactor (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_fkPrefactor_pos_comp_pOfBeta T

/--
[eventually_fk_length_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_length_scaling_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), T.fkCorrelationLength p = T.fkPrefactor p * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_fk_length_scaling T

/--
[eventually_fk_length_scaling_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_length_scaling_comp_pOfBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.fkCorrelationLength (IsingFK.pOfBeta β) = T.fkPrefactor (IsingFK.pOfBeta β) * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - IsingFK.pOfBeta β)) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_fk_length_scaling_comp_pOfBeta T

/--
[eventually_ising_fk_length_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_ising_fk_length_agree_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.isingCorrelationLength β = T.fkCorrelationLength (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_ising_fk_length_agree T

/--
[fk_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma fk_hasCriticalNu_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) T.fkCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.fk_hasCriticalNu T

/--
[toFKTarget_isingCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toFKTarget_isingCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  T.toFKTarget.isingCorrelationLength = T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.toFKTarget_isingCorrelationLength T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.hasCriticalNu T

/--
[eventually_isingCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_isingCorrelationLength_eq_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.isingCorrelationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.eventually_isingCorrelationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.rgToExponentBridge T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
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
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[congr_predictedExponent_toFKTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toFKTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toFKTarget = FKToIsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toFKTarget := by
-- proof
  apply StatMech.Exact3D.FKPowerLawToIsingAnalyticRGToExponentTarget.congr_predictedExponent_toFKTarget hpred T

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.isingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.hasCorrelationLength T hβ

/--
[eventually_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_betaLeftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_mem_betaLeftCriticalInterval T

/--
[eventually_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_pLeftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3)) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_mem_pLeftCriticalInterval T

/--
[eventually_pOfBeta_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pOfBeta_mem_pLeftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), IsingFK.pOfBeta β ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3)) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_pOfBeta_mem_pLeftCriticalInterval T

/--
[betaC_sub_pos_of_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_betaLeftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.betaC_sub_pos_of_mem_betaLeftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.betaδ := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval T hβ

/--
[pCritical_sub_pos_of_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma pCritical_sub_pos_of_mem_pLeftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3))) :
-- imply
  0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.pCritical_sub_pos_of_mem_pLeftCriticalInterval T hp

/--
[pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3))) :
-- imply
  IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval T hp

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.betaδ := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_pCritical_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pCritical_sub_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), 0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_pCritical_sub_pos T

/--
[eventually_pCritical_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pCritical_sub_lt_delta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_pCritical_sub_lt_delta T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.isingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_fkMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkMass_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), 0 < T.fkMass p := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_fkMass_pos T

/--
[eventually_fkMass_pos_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkMass_pos_comp_pOfBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.fkMass (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_fkMass_pos_comp_pOfBeta T

/--
[eventually_fk_length_eq_inv_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_length_eq_inv_mass_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), T.fkCorrelationLength p = (T.fkMass p)⁻¹ := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_fk_length_eq_inv_mass T

/--
[eventually_fk_length_eq_inv_mass_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_length_eq_inv_mass_comp_pOfBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.fkCorrelationLength (IsingFK.pOfBeta β) = (T.fkMass (IsingFK.pOfBeta β))⁻¹ := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_fk_length_eq_inv_mass_comp_pOfBeta T

/--
[eventually_fkPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkPrefactor_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), 0 < T.fkPrefactor p := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_fkPrefactor_pos T

/--
[eventually_fkPrefactor_pos_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkPrefactor_pos_comp_pOfBeta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.fkPrefactor (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_fkPrefactor_pos_comp_pOfBeta T

/--
[eventually_fk_length_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_length_scaling_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), T.fkCorrelationLength p = T.fkPrefactor p * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_fk_length_scaling T

/--
[eventually_fk_length_scaling_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_length_scaling_comp_pOfBeta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.fkCorrelationLength (IsingFK.pOfBeta β) = T.fkPrefactor (IsingFK.pOfBeta β) * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - IsingFK.pOfBeta β)) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_fk_length_scaling_comp_pOfBeta T

/--
[eventually_ising_fk_length_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_ising_fk_length_agree_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.isingCorrelationLength β = T.fkCorrelationLength (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_ising_fk_length_agree T

/--
[fk_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma fk_hasCriticalNu_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) T.fkCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.fk_hasCriticalNu T

/--
[toFKPowerLawTarget_toFKTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toFKPowerLawTarget_toFKTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  T.toFKPowerLawTarget.toFKTarget = T.toFKTarget := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.toFKPowerLawTarget_toFKTarget T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.hasCriticalNu T

/--
[eventually_isingCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_isingCorrelationLength_eq_liminfCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.isingCorrelationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.eventually_isingCorrelationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.rgToExponentBridge T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
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
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_3
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_3
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_3
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[congr_predictedExponent_toFKPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toFKPowerLawTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toFKPowerLawTarget = FKPowerLawToIsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toFKPowerLawTarget := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.congr_predictedExponent_toFKPowerLawTarget hpred T

/--
[congr_predictedExponent_toFKTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toFKTarget_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toFKTarget = FKToIsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toFKTarget := by
-- proof
  apply StatMech.Exact3D.FKMassAnalyticRGToExponentTarget.congr_predictedExponent_toFKTarget hpred T

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.isingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.hasCorrelationLength T hβ

/--
[fkMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma fkMass_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3))) :
-- imply
  0 < T.fkMass p := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.fkMass_pos T hp

/--
[eventually_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_betaLeftCriticalInterval_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_mem_betaLeftCriticalInterval T

/--
[eventually_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mem_pLeftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3)) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_mem_pLeftCriticalInterval T

/--
[eventually_pOfBeta_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pOfBeta_mem_pLeftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), IsingFK.pOfBeta β ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3)) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_pOfBeta_mem_pLeftCriticalInterval T

/--
[betaC_sub_pos_of_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_betaLeftCriticalInterval_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.betaC_sub_pos_of_mem_betaLeftCriticalInterval T hβ

/--
[betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
  {β : ℝ}
-- given
  (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.betaδ) (Ising.betaC 3)) :
-- imply
  Ising.betaC 3 - β < T.betaδ := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.betaC_sub_lt_delta_of_mem_betaLeftCriticalInterval T hβ

/--
[pCritical_sub_pos_of_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma pCritical_sub_pos_of_mem_pLeftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3))) :
-- imply
  0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.pCritical_sub_pos_of_mem_pLeftCriticalInterval T hp

/--
[pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3))) :
-- imply
  IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.pCritical_sub_lt_delta_of_mem_pLeftCriticalInterval T hp

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.betaδ := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_betaC_sub_lt_delta T

/--
[eventually_pCritical_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pCritical_sub_pos_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), 0 < IsingFK.pOfBeta (Ising.betaC 3) - p := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_pCritical_sub_pos T

/--
[eventually_pCritical_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_pCritical_sub_lt_delta_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), IsingFK.pOfBeta (Ising.betaC 3) - p < T.pδ := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_pCritical_sub_lt_delta T

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.isingCorrelationLength β) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_hasCorrelationLength T

/--
[eventually_fkMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkMass_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), 0 < T.fkMass p := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_fkMass_pos T

/--
[eventually_fkMass_pos_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkMass_pos_comp_pOfBeta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.fkMass (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_fkMass_pos_comp_pOfBeta T

/--
[eventually_fkMassPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkMassPrefactor_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), 0 < T.fkMassPrefactor p := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_fkMassPrefactor_pos T

/--
[eventually_fkMassPrefactor_pos_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fkMassPrefactor_pos_comp_pOfBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.fkMassPrefactor (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_fkMassPrefactor_pos_comp_pOfBeta T

/--
[eventually_fk_mass_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_mass_scaling_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), T.fkMass p = T.fkMassPrefactor p * Real.exp (C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_fk_mass_scaling T

/--
[eventually_fk_mass_scaling_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_mass_scaling_comp_pOfBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.fkMass (IsingFK.pOfBeta β) = T.fkMassPrefactor (IsingFK.pOfBeta β) * Real.exp (C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - IsingFK.pOfBeta β)) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_fk_mass_scaling_comp_pOfBeta T

/--
[eventually_fk_length_eq_inv_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_length_eq_inv_mass_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ p in nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3))), T.fkCorrelationLength p = (T.fkMass p)⁻¹ := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_fk_length_eq_inv_mass T

/--
[eventually_fk_length_eq_inv_mass_comp_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_fk_length_eq_inv_mass_comp_pOfBeta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.fkCorrelationLength (IsingFK.pOfBeta β) = (T.fkMass (IsingFK.pOfBeta β))⁻¹ := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_fk_length_eq_inv_mass_comp_pOfBeta T

/--
[eventually_ising_fk_length_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_ising_fk_length_agree_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.isingCorrelationLength β = T.fkCorrelationLength (IsingFK.pOfBeta β) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_ising_fk_length_agree T

/--
[fkLengthScalingFromMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma fkLengthScalingFromMass_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - T.pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → T.fkCorrelationLength p = (T.fkMassPrefactor p)⁻¹ * Real.exp (-C.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.fkLengthScalingFromMass T

/--
[toFKMassTarget_toFKPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toFKMassTarget_toFKPowerLawTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  T.toFKMassTarget.toFKPowerLawTarget = T.toFKPowerLawTarget := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.toFKMassTarget_toFKPowerLawTarget T

/--
[fk_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma fk_hasCriticalNu_eq_3
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) T.fkCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.fk_hasCriticalNu T

/--
[toFKMassTarget_toFKTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toFKMassTarget_toFKTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  T.toFKMassTarget.toFKTarget = T.toFKTarget := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.toFKMassTarget_toFKTarget T

/--
[toFKPowerLawTarget_toFKTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma toFKPowerLawTarget_toFKTarget_eq_2
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  T.toFKPowerLawTarget.toFKTarget = T.toFKTarget := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.toFKPowerLawTarget_toFKTarget T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.hasCriticalNu T

/--
[eventually_isingCorrelationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_isingCorrelationLength_eq_liminfCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.isingCorrelationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.eventually_isingCorrelationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.rgToExponentBridge T

/--
[rgToExponentBridge_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_direct_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.rgToExponentBridge_direct T

/--
[hasCriticalNu_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_direct_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.hasCriticalNu_direct T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_direct_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.valid_of_checks_direct T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq_4
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
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
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_4
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_4
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.hasCriticalNu_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_4
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[congr_predictedExponent_toFKMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toFKMassTarget_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toFKMassTarget = FKMassAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toFKMassTarget := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.congr_predictedExponent_toFKMassTarget hpred T

/--
[congr_predictedExponent_toFKPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toFKPowerLawTarget_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toFKPowerLawTarget = FKPowerLawToIsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toFKPowerLawTarget := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.congr_predictedExponent_toFKPowerLawTarget hpred T

/--
[congr_predictedExponent_toFKTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_toFKTarget_eq_3
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  (T.congr_predictedExponent hpred).toFKTarget = FKToIsingAnalyticRGToExponentTarget.congr_predictedExponent hpred T.toFKTarget := by
-- proof
  apply StatMech.Exact3D.FKMassPowerLawToIsingAnalyticRGToExponentTarget.congr_predictedExponent_toFKTarget hpred T


-- created on 2026-10-23
