import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.IsingFinitePlusTailBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailHyperbolicSplitting StatMech.Exact3D.FinitePlusTailBlockRGPackage StatMech.Exact3D.FinitePlusTailClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingAnalyticTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingAnalyticTarget H scale T

/--
[certificate_valid_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingAnalyticTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingAnalyticTarget H scale T

/--
[certificate_hasCriticalNu_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingAnalyticTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingAnalyticTarget H scale T

/--
[certificate_rgToExponentBridge_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassAnalyticTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingMassAnalyticTarget H scale T

/--
[certificate_valid_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassAnalyticTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingMassAnalyticTarget H scale T

/--
[certificate_hasCriticalNu_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassAnalyticTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingMassAnalyticTarget H scale T

/--
[certificate_rgToExponentBridge_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassPowerLawTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingMassPowerLawTarget H scale T

/--
[certificate_valid_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassPowerLawTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingMassPowerLawTarget H scale T

/--
[certificate_hasCriticalNu_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassPowerLawTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingMassPowerLawTarget H scale T

/--
[certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget H scale T

/--
[certificate_valid_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeAnalyticToPlusTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_freeAnalyticToPlusTarget H scale T

/--
[certificate_hasCriticalNu_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_freeAnalyticToPlusTarget H scale T

/--
[certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget H scale T

/--
[certificate_valid_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassAnalyticToPlusTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_freeMassAnalyticToPlusTarget H scale T

/--
[certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget H scale T

/--
[certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget H scale T

/--
[certificate_valid_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassPowerLawToPlusTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_freeMassPowerLawToPlusTarget H scale T

/--
[certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget H scale T

/--
[certificate_valid_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingAnalyticTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs H scale T

/--
[certificate_valid_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingRGCoordinateBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingRGCoordinateBridgeInputs H scale T

/--
[certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs H scale T

/--
[certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs H scale T

/--
[certificate_valid_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassRGCoordinateBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (H.certificate scale Ising3DModel)} :
-- imply
  (H.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingMassRGCoordinateBridgeInputs H scale T

/--
[certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (H.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs H scale T

/--
[certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent H scale hpred T

/--
[certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (H.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent H scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (hpred : (H.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (H.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent H scale hpred T

/--
[certificate_rgToExponentBridge_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingAnalyticTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingAnalyticTarget P scale T

/--
[certificate_rgToExponentBridge_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassAnalyticTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingMassAnalyticTarget P scale T

/--
[certificate_rgToExponentBridge_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassPowerLawTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingMassPowerLawTarget P scale T

/--
[certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget P scale T

/--
[certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget P scale T

/--
[certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget P scale T

/--
[certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingAnalyticTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingAnalyticTarget P scale T

/--
[certificate_hasCriticalNu_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingAnalyticTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingAnalyticTarget P scale T

/--
[certificate_valid_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassAnalyticTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingMassAnalyticTarget P scale T

/--
[certificate_hasCriticalNu_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassAnalyticTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingMassAnalyticTarget P scale T

/--
[certificate_valid_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassPowerLawTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingMassPowerLawTarget P scale T

/--
[certificate_hasCriticalNu_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassPowerLawTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingMassPowerLawTarget P scale T

/--
[certificate_valid_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeAnalyticToPlusTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_freeAnalyticToPlusTarget P scale T

/--
[certificate_hasCriticalNu_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_freeAnalyticToPlusTarget P scale T

/--
[certificate_valid_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassAnalyticToPlusTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_freeMassAnalyticToPlusTarget P scale T

/--
[certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget P scale T

/--
[certificate_valid_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassPowerLawToPlusTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_freeMassPowerLawToPlusTarget P scale T

/--
[certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget P scale T

/--
[certificate_valid_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingAnalyticTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs P scale T

/--
[certificate_valid_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingRGCoordinateBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingRGCoordinateBridgeInputs P scale T

/--
[certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs P scale T

/--
[certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs P scale T

/--
[certificate_valid_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassRGCoordinateBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingMassRGCoordinateBridgeInputs P scale T

/--
[certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs P scale T

/--
[certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingAnalyticTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingAnalyticTarget P scale T

/--
[certificate_rgToExponentBridge_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassAnalyticTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassAnalyticTarget P scale T

/--
[certificate_rgToExponentBridge_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassPowerLawTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassPowerLawTarget P scale T

/--
[certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget P scale T

/--
[certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget P scale T

/--
[certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget P scale T

/--
[certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingAnalyticTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingAnalyticTarget P scale T

/--
[certificate_hasCriticalNu_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingAnalyticTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingAnalyticTarget P scale T

/--
[certificate_valid_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassAnalyticTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingMassAnalyticTarget P scale T

/--
[certificate_hasCriticalNu_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassAnalyticTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassAnalyticTarget P scale T

/--
[certificate_valid_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassPowerLawTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingMassPowerLawTarget P scale T

/--
[certificate_hasCriticalNu_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassPowerLawTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassPowerLawTarget P scale T

/--
[certificate_valid_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeAnalyticToPlusTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_freeAnalyticToPlusTarget P scale T

/--
[certificate_hasCriticalNu_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_freeAnalyticToPlusTarget P scale T

/--
[certificate_valid_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassAnalyticToPlusTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_freeMassAnalyticToPlusTarget P scale T

/--
[certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget P scale T

/--
[certificate_valid_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassPowerLawToPlusTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_freeMassPowerLawToPlusTarget P scale T

/--
[certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget P scale T

/--
[certificate_valid_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingAnalyticTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs P scale T

/--
[certificate_valid_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingRGCoordinateBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingRGCoordinateBridgeInputs P scale T

/--
[certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs P scale T

/--
[certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs P scale T

/--
[certificate_valid_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassRGCoordinateBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingMassRGCoordinateBridgeInputs P scale T

/--
[certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (P.certificate scale Ising3DModel)} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs P scale T

/--
[certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale Ising3DModel).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingFinitePlusTailBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (hpred : (P.certificate scale Ising3DModel).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale Ising3DModel).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T


-- created on 2026-10-23
