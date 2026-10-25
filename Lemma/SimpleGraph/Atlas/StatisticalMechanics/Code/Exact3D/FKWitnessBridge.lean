import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FKWitnessBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteWitnessPackage StatMech.Exact3D.InfiniteTailWitnessPackage StatMech.Exact3D.InfiniteTailTableWitnessPackage


/--
[rgToExponentBridge_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkTarget_eq
  [DecidableEq α]
  {T : FKToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fkTarget W T

/--
[valid_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkTarget_eq
  [DecidableEq α]
  {T : FKToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fkTarget W T

/--
[hasCriticalNu_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkTarget_eq
  [DecidableEq α]
  {T : FKToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fkTarget W T

/--
[rgToExponentBridge_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkPowerLawTarget_eq
  [DecidableEq α]
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fkPowerLawTarget W T

/--
[valid_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkPowerLawTarget_eq
  [DecidableEq α]
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fkPowerLawTarget W T

/--
[hasCriticalNu_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkPowerLawTarget_eq
  [DecidableEq α]
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fkPowerLawTarget W T

/--
[rgToExponentBridge_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassTarget_eq
  [DecidableEq α]
  {T : FKMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fkMassTarget W T

/--
[valid_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassTarget_eq
  [DecidableEq α]
  {T : FKMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fkMassTarget W T

/--
[hasCriticalNu_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassTarget_eq
  [DecidableEq α]
  {T : FKMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fkMassTarget W T

/--
[rgToExponentBridge_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassPowerLawTarget_eq
  [DecidableEq α]
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fkMassPowerLawTarget W T

/--
[valid_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassPowerLawTarget_eq
  [DecidableEq α]
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fkMassPowerLawTarget W T

/--
[hasCriticalNu_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassPowerLawTarget_eq
  [DecidableEq α]
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fkMassPowerLawTarget W T

/--
[valid_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fkTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fkTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fkTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent W hpred T

/--
[valid_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkPowerLawTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fkPowerLawTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fkMassTarget_congr_predictedExponent W hpred T

/--
[valid_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fkMassTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fkMassTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[valid_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassPowerLawTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fkMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_eventually_eq_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength W.certificate.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fk_pOfBeta_eventually_eq W hfk hEq

/--
[valid_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_eventually_eq_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength W.certificate.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fk_pOfBeta_eventually_eq W hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_eventually_eq_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength W.certificate.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fk_pOfBeta_eventually_eq W hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent W hpred hfk hEq

/--
[valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent W hpred hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent W hpred hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hfk : (W.certificate.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq W hfk hEq

/--
[valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hfk : (W.certificate.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq W hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hfk : (W.certificate.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq W hfk hEq

/--
[rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[valid_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fk_exact_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[rgToExponentBridge_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkTarget_eq_2
  [DecidableEq α]
  {T : FKToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fkTarget W T

/--
[valid_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkTarget_eq_2
  [DecidableEq α]
  {T : FKToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fkTarget W T

/--
[hasCriticalNu_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkTarget_eq_2
  [DecidableEq α]
  {T : FKToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fkTarget W T

/--
[rgToExponentBridge_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkPowerLawTarget_eq_2
  [DecidableEq α]
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fkPowerLawTarget W T

/--
[valid_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkPowerLawTarget_eq_2
  [DecidableEq α]
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fkPowerLawTarget W T

/--
[hasCriticalNu_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkPowerLawTarget_eq_2
  [DecidableEq α]
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fkPowerLawTarget W T

/--
[rgToExponentBridge_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassTarget_eq_2
  [DecidableEq α]
  {T : FKMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fkMassTarget W T

/--
[valid_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassTarget_eq_2
  [DecidableEq α]
  {T : FKMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fkMassTarget W T

/--
[hasCriticalNu_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassTarget_eq_2
  [DecidableEq α]
  {T : FKMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fkMassTarget W T

/--
[rgToExponentBridge_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassPowerLawTarget_eq_2
  [DecidableEq α]
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fkMassPowerLawTarget W T

/--
[valid_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassPowerLawTarget_eq_2
  [DecidableEq α]
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fkMassPowerLawTarget W T

/--
[hasCriticalNu_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassPowerLawTarget_eq_2
  [DecidableEq α]
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fkMassPowerLawTarget W T

/--
[valid_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fkTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fkTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fkTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent W hpred T

/--
[valid_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkPowerLawTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fkPowerLawTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fkMassTarget_congr_predictedExponent W hpred T

/--
[valid_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fkMassTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fkMassTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[valid_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassPowerLawTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fkMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_eventually_eq_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength W.certificate.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fk_pOfBeta_eventually_eq W hfk hEq

/--
[valid_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_eventually_eq_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength W.certificate.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fk_pOfBeta_eventually_eq W hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_eventually_eq_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength W.certificate.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fk_pOfBeta_eventually_eq W hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent W hpred hfk hEq

/--
[valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent W hpred hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent W hpred hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hfk : (W.certificate.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq W hfk hEq

/--
[valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hfk : (W.certificate.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq W hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hfk : (W.certificate.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq W hfk hEq

/--
[rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[valid_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fk_exact_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[rgToExponentBridge_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fkTarget W T

/--
[valid_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fkTarget W T

/--
[hasCriticalNu_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fkTarget W T

/--
[rgToExponentBridge_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkPowerLawTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fkPowerLawTarget W T

/--
[valid_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkPowerLawTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fkPowerLawTarget W T

/--
[hasCriticalNu_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkPowerLawTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fkPowerLawTarget W T

/--
[rgToExponentBridge_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fkMassTarget W T

/--
[valid_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fkMassTarget W T

/--
[hasCriticalNu_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fkMassTarget W T

/--
[rgToExponentBridge_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassPowerLawTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fkMassPowerLawTarget W T

/--
[valid_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassPowerLawTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fkMassPowerLawTarget W T

/--
[hasCriticalNu_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassPowerLawTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fkMassPowerLawTarget W T

/--
[valid_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fkTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fkTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fkTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent W hpred T

/--
[valid_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkPowerLawTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fkPowerLawTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fkMassTarget_congr_predictedExponent W hpred T

/--
[valid_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fkMassTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fkMassTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[valid_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fkMassPowerLawTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fkMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength W.certificate.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fk_pOfBeta_eventually_eq W hfk hEq

/--
[valid_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength W.certificate.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fk_pOfBeta_eventually_eq W hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength W.certificate.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fk_pOfBeta_eventually_eq W hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent W hpred hfk hEq

/--
[valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent W hpred hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent W hpred hfk hEq

/--
[rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hfk : (W.certificate.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq W hfk hEq

/--
[valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hfk : (W.certificate.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq W hfk hEq

/--
[hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hfk : (W.certificate.retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq W hfk hEq

/--
[rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[valid_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fk_exact_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (W.certificate.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  W.certificate.Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq


-- created on 2026-10-23
