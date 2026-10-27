import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FKFinitePlusTailBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailHyperbolicSplitting StatMech.Exact3D.FinitePlusTailBlockRGPackage StatMech.Exact3D.FinitePlusTailClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fkTarget H scale T

/--
[certificate_valid_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fkTarget H scale T

/--
[certificate_hasCriticalNu_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fkTarget H scale T

/--
[certificate_rgToExponentBridge_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkPowerLawTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fkPowerLawTarget H scale T

/--
[certificate_valid_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkPowerLawTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fkPowerLawTarget H scale T

/--
[certificate_hasCriticalNu_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkPowerLawTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fkPowerLawTarget H scale T

/--
[certificate_rgToExponentBridge_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fkMassTarget H scale T

/--
[certificate_valid_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fkMassTarget H scale T

/--
[certificate_hasCriticalNu_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fkMassTarget H scale T

/--
[certificate_rgToExponentBridge_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassPowerLawTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fkMassPowerLawTarget H scale T

/--
[certificate_valid_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassPowerLawTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fkMassPowerLawTarget H scale T

/--
[certificate_hasCriticalNu_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassPowerLawTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fkMassPowerLawTarget H scale T

/--
[certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fkTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkPowerLawTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fkPowerLawTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fkMassTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (H.certificate scale Ising3DModel).predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq H scale hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (H.certificate scale Ising3DModel).predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fk_pOfBeta_eventually_eq H scale hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (H.certificate scale Ising3DModel).predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq H scale hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent H scale hpred hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent H scale hpred hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent H scale hpred hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : ((H.certificate scale Ising3DModel).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq H scale hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : ((H.certificate scale Ising3DModel).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq H scale hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : ((H.certificate scale Ising3DModel).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq H scale hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(H.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo H scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(H.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo H scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(H.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo H scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((H.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo H scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((H.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo H scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((H.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo H scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (H.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_rgToExponentBridge_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fkTarget P scale T

/--
[certificate_valid_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fkTarget P scale T

/--
[certificate_hasCriticalNu_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fkTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkPowerLawTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fkPowerLawTarget P scale T

/--
[certificate_valid_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkPowerLawTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fkPowerLawTarget P scale T

/--
[certificate_hasCriticalNu_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkPowerLawTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fkPowerLawTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fkMassTarget P scale T

/--
[certificate_valid_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fkMassTarget P scale T

/--
[certificate_hasCriticalNu_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fkMassTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassPowerLawTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fkMassPowerLawTarget P scale T

/--
[certificate_valid_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassPowerLawTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fkMassPowerLawTarget P scale T

/--
[certificate_hasCriticalNu_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassPowerLawTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fkMassPowerLawTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fkTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkPowerLawTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fkPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fkMassTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (P.certificate scale Ising3DModel).predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq P scale hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (P.certificate scale Ising3DModel).predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fk_pOfBeta_eventually_eq P scale hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (P.certificate scale Ising3DModel).predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq P scale hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent P scale hpred hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent P scale hpred hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent P scale hpred hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : ((P.certificate scale Ising3DModel).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq P scale hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : ((P.certificate scale Ising3DModel).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq P scale hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : ((P.certificate scale Ising3DModel).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq P scale hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_rgToExponentBridge_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fkTarget P scale T

/--
[certificate_valid_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fkTarget P scale T

/--
[certificate_hasCriticalNu_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fkTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkPowerLawTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fkPowerLawTarget P scale T

/--
[certificate_valid_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkPowerLawTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fkPowerLawTarget P scale T

/--
[certificate_hasCriticalNu_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkPowerLawTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fkPowerLawTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fkMassTarget P scale T

/--
[certificate_valid_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fkMassTarget P scale T

/--
[certificate_hasCriticalNu_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fkMassTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassPowerLawTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fkMassPowerLawTarget P scale T

/--
[certificate_valid_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassPowerLawTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fkMassPowerLawTarget P scale T

/--
[certificate_hasCriticalNu_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassPowerLawTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fkMassPowerLawTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fkTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkPowerLawTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fkPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fkMassTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (P.certificate scale Ising3DModel).predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq P scale hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (P.certificate scale Ising3DModel).predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fk_pOfBeta_eventually_eq P scale hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (P.certificate scale Ising3DModel).predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq P scale hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent P scale hpred hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent P scale hpred hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent P scale hpred hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : ((P.certificate scale Ising3DModel).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq P scale hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : ((P.certificate scale Ising3DModel).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq P scale hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (hfk : ((P.certificate scale Ising3DModel).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq P scale hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkPrefactor pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pDelta hpDelta hpref_pos hlogpref hscaling hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((P.certificate scale Ising3DModel).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  (P.certificate scale Ising3DModel).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pDelta : ℝ}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent)
  (hpDelta : 0 < pDelta)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pDelta) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ beta in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength beta = fkCorrelationLength (IsingFK.pOfBeta beta)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pDelta hpDelta hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq


-- created on 2026-10-23
