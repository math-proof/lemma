import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.IsingWitnessBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteWitnessPackage StatMech.Exact3D.InfiniteTailWitnessPackage StatMech.Exact3D.InfiniteTailTableWitnessPackage


/--
[rgToExponentBridge_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingAnalyticTarget_eq
  [DecidableEq α]
  {T : IsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingAnalyticTarget W T

/--
[valid_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingAnalyticTarget_eq
  [DecidableEq α]
  {T : IsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingAnalyticTarget W T

/--
[hasCriticalNu_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingAnalyticTarget_eq
  [DecidableEq α]
  {T : IsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingAnalyticTarget W T

/--
[rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassAnalyticTarget_eq
  [DecidableEq α]
  {T : IsingMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingMassAnalyticTarget W T

/--
[valid_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassAnalyticTarget_eq
  [DecidableEq α]
  {T : IsingMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingMassAnalyticTarget W T

/--
[hasCriticalNu_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassAnalyticTarget_eq
  [DecidableEq α]
  {T : IsingMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingMassAnalyticTarget W T

/--
[rgToExponentBridge_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassPowerLawTarget_eq
  [DecidableEq α]
  {T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingMassPowerLawTarget W T

/--
[valid_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassPowerLawTarget_eq
  [DecidableEq α]
  {T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingMassPowerLawTarget W T

/--
[hasCriticalNu_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassPowerLawTarget_eq
  [DecidableEq α]
  {T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingMassPowerLawTarget W T

/--
[rgToExponentBridge_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeAnalyticToPlusTarget_eq
  [DecidableEq α]
  {T : FreeAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_freeAnalyticToPlusTarget W T

/--
[valid_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeAnalyticToPlusTarget_eq
  [DecidableEq α]
  {T : FreeAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_freeAnalyticToPlusTarget W T

/--
[hasCriticalNu_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeAnalyticToPlusTarget_eq
  [DecidableEq α]
  {T : FreeAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_freeAnalyticToPlusTarget W T

/--
[rgToExponentBridge_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassAnalyticToPlusTarget_eq
  [DecidableEq α]
  {T : FreeMassAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_freeMassAnalyticToPlusTarget W T

/--
[valid_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassAnalyticToPlusTarget_eq
  [DecidableEq α]
  {T : FreeMassAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_freeMassAnalyticToPlusTarget W T

/--
[hasCriticalNu_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassAnalyticToPlusTarget_eq
  [DecidableEq α]
  {T : FreeMassAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_freeMassAnalyticToPlusTarget W T

/--
[rgToExponentBridge_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassPowerLawToPlusTarget_eq
  [DecidableEq α]
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_freeMassPowerLawToPlusTarget W T

/--
[valid_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassPowerLawToPlusTarget_eq
  [DecidableEq α]
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_freeMassPowerLawToPlusTarget W T

/--
[hasCriticalNu_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassPowerLawToPlusTarget_eq
  [DecidableEq α]
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_freeMassPowerLawToPlusTarget W T

/--
[valid_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingAnalyticTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingAnalyticTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent W hpred T

/--
[valid_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassAnalyticTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingMassAnalyticTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[valid_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassPowerLawTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[valid_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_freeAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent W hpred T

/--
[valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingRGCoordinateBridgeInputs_eq
  [DecidableEq α]
  {T : IsingRGCoordinateBridgeInputs W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingRGCoordinateBridgeInputs W T

/--
[valid_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingRGCoordinateBridgeInputs_eq
  [DecidableEq α]
  {T : IsingRGCoordinateBridgeInputs W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingRGCoordinateBridgeInputs W T

/--
[hasCriticalNu_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingRGCoordinateBridgeInputs_eq
  [DecidableEq α]
  {T : IsingRGCoordinateBridgeInputs W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingRGCoordinateBridgeInputs W T

/--
[rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_eq
  [DecidableEq α]
  {T : IsingMassRGCoordinateBridgeInputs W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs W T

/--
[valid_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassRGCoordinateBridgeInputs_eq
  [DecidableEq α]
  {T : IsingMassRGCoordinateBridgeInputs W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingMassRGCoordinateBridgeInputs W T

/--
[hasCriticalNu_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_eq
  [DecidableEq α]
  {T : IsingMassRGCoordinateBridgeInputs W.certificate}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingMassRGCoordinateBridgeInputs W T

/--
[rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (W : FiniteWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingAnalyticTarget_eq_2
  [DecidableEq α]
  {T : IsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingAnalyticTarget W T

/--
[rgToExponentBridge_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassAnalyticTarget_eq_2
  [DecidableEq α]
  {T : IsingMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingMassAnalyticTarget W T

/--
[rgToExponentBridge_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassPowerLawTarget_eq_2
  [DecidableEq α]
  {T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingMassPowerLawTarget W T

/--
[rgToExponentBridge_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeAnalyticToPlusTarget_eq_2
  [DecidableEq α]
  {T : FreeAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_freeAnalyticToPlusTarget W T

/--
[rgToExponentBridge_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassAnalyticToPlusTarget_eq_2
  [DecidableEq α]
  {T : FreeMassAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_freeMassAnalyticToPlusTarget W T

/--
[rgToExponentBridge_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassPowerLawToPlusTarget_eq_2
  [DecidableEq α]
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_freeMassPowerLawToPlusTarget W T

/--
[rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent W hpred T

/--
[valid_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingAnalyticTarget_eq_2
  [DecidableEq α]
  {T : IsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingAnalyticTarget W T

/--
[hasCriticalNu_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingAnalyticTarget_eq_2
  [DecidableEq α]
  {T : IsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingAnalyticTarget W T

/--
[valid_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassAnalyticTarget_eq_2
  [DecidableEq α]
  {T : IsingMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingMassAnalyticTarget W T

/--
[hasCriticalNu_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassAnalyticTarget_eq_2
  [DecidableEq α]
  {T : IsingMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingMassAnalyticTarget W T

/--
[valid_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassPowerLawTarget_eq_2
  [DecidableEq α]
  {T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingMassPowerLawTarget W T

/--
[hasCriticalNu_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassPowerLawTarget_eq_2
  [DecidableEq α]
  {T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingMassPowerLawTarget W T

/--
[valid_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeAnalyticToPlusTarget_eq_2
  [DecidableEq α]
  {T : FreeAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_freeAnalyticToPlusTarget W T

/--
[hasCriticalNu_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeAnalyticToPlusTarget_eq_2
  [DecidableEq α]
  {T : FreeAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_freeAnalyticToPlusTarget W T

/--
[valid_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassAnalyticToPlusTarget_eq_2
  [DecidableEq α]
  {T : FreeMassAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_freeMassAnalyticToPlusTarget W T

/--
[hasCriticalNu_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassAnalyticToPlusTarget_eq_2
  [DecidableEq α]
  {T : FreeMassAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_freeMassAnalyticToPlusTarget W T

/--
[valid_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassPowerLawToPlusTarget_eq_2
  [DecidableEq α]
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_freeMassPowerLawToPlusTarget W T

/--
[hasCriticalNu_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassPowerLawToPlusTarget_eq_2
  [DecidableEq α]
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_freeMassPowerLawToPlusTarget W T

/--
[valid_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingAnalyticTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingAnalyticTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent W hpred T

/--
[valid_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassAnalyticTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingMassAnalyticTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent W hpred T

/--
[valid_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassPowerLawTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[valid_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_freeAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingRGCoordinateBridgeInputs_eq_2
  [DecidableEq α]
  {T : IsingRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingRGCoordinateBridgeInputs W T

/--
[valid_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingRGCoordinateBridgeInputs_eq_2
  [DecidableEq α]
  {T : IsingRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingRGCoordinateBridgeInputs W T

/--
[hasCriticalNu_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingRGCoordinateBridgeInputs_eq_2
  [DecidableEq α]
  {T : IsingRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingRGCoordinateBridgeInputs W T

/--
[rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_eq_2
  [DecidableEq α]
  {T : IsingMassRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs W T

/--
[valid_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassRGCoordinateBridgeInputs_eq_2
  [DecidableEq α]
  {T : IsingMassRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingMassRGCoordinateBridgeInputs W T

/--
[hasCriticalNu_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_eq_2
  [DecidableEq α]
  {T : IsingMassRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingMassRGCoordinateBridgeInputs W T

/--
[rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailWitnessPackage (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingAnalyticTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingAnalyticTarget W T

/--
[rgToExponentBridge_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassAnalyticTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingMassAnalyticTarget W T

/--
[rgToExponentBridge_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassPowerLawTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingMassPowerLawTarget W T

/--
[rgToExponentBridge_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeAnalyticToPlusTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FreeAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_freeAnalyticToPlusTarget W T

/--
[rgToExponentBridge_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassAnalyticToPlusTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FreeMassAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_freeMassAnalyticToPlusTarget W T

/--
[rgToExponentBridge_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassPowerLawToPlusTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_freeMassPowerLawToPlusTarget W T

/--
[rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent W hpred T

/--
[valid_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingAnalyticTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingAnalyticTarget W T

/--
[hasCriticalNu_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingAnalyticTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingAnalyticTarget W T

/--
[valid_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassAnalyticTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingMassAnalyticTarget W T

/--
[hasCriticalNu_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassAnalyticTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingMassAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingMassAnalyticTarget W T

/--
[valid_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassPowerLawTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingMassPowerLawTarget W T

/--
[hasCriticalNu_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassPowerLawTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingMassPowerLawAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingMassPowerLawTarget W T

/--
[valid_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeAnalyticToPlusTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FreeAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_freeAnalyticToPlusTarget W T

/--
[hasCriticalNu_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeAnalyticToPlusTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FreeAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_freeAnalyticToPlusTarget W T

/--
[valid_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassAnalyticToPlusTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FreeMassAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_freeMassAnalyticToPlusTarget W T

/--
[hasCriticalNu_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassAnalyticToPlusTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FreeMassAnalyticRGToPlusExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_freeMassAnalyticToPlusTarget W T

/--
[valid_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassPowerLawToPlusTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_freeMassPowerLawToPlusTarget W T

/--
[hasCriticalNu_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassPowerLawToPlusTarget_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_freeMassPowerLawToPlusTarget W T

/--
[valid_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingAnalyticTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingAnalyticTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent W hpred T

/--
[valid_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassAnalyticTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingMassAnalyticTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent W hpred T

/--
[valid_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassPowerLawTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent W hpred T

/--
[valid_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_freeAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent W hpred T

/--
[valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingRGCoordinateBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingRGCoordinateBridgeInputs W T

/--
[valid_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingRGCoordinateBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingRGCoordinateBridgeInputs W T

/--
[hasCriticalNu_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingRGCoordinateBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingRGCoordinateBridgeInputs W T

/--
[rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingMassRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs W T

/--
[valid_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassRGCoordinateBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingMassRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingMassRGCoordinateBridgeInputs W T

/--
[hasCriticalNu_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {T : IsingMassRGCoordinateBridgeInputs W.certificate}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingMassRGCoordinateBridgeInputs W T

/--
[rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  W.certificate.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent W hpred T

/--
[hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingWitnessBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) Ising3DModel)
  (hpred : W.certificate.predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent W hpred T


-- created on 2026-10-23
