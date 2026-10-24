import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.FinitePlusTailAnalyticBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailHyperbolicSplitting StatMech.Exact3D.FinitePlusTailBlockRGPackage StatMech.Exact3D.FinitePlusTailClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticBridgeInputs (H.certificate scale M) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_analyticBridgeInputs H scale M h

/--
[certificate_valid_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticBridgeInputs (H.certificate scale M) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_analyticBridgeInputs H scale M h

/--
[certificate_hasCriticalNu_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticBridgeInputs (H.certificate scale M) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_analyticBridgeInputs H scale M h

/--
[certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent H scale M hpred h

/--
[certificate_valid_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_analyticBridgeInputs_congr_predictedExponent H scale M hpred h

/--
[certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent H scale M hpred h

/--
[certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (H.certificate scale M) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs H scale M h

/--
[certificate_valid_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticPrefactorBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (H.certificate scale M) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_analyticPrefactorBridgeInputs H scale M h

/--
[certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (H.certificate scale M) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs H scale M h

/--
[certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent H scale M hpred h

/--
[certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent H scale M hpred h

/--
[certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent H scale M hpred h

/--
[certificate_rgToExponentBridge_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticMassBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticMassBridgeInputs (H.certificate scale M) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_analyticMassBridgeInputs H scale M h

/--
[certificate_valid_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticMassBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticMassBridgeInputs (H.certificate scale M) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_analyticMassBridgeInputs H scale M h

/--
[certificate_hasCriticalNu_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticMassBridgeInputs_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticMassBridgeInputs (H.certificate scale M) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_analyticMassBridgeInputs H scale M h

/--
[certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent H scale M hpred h

/--
[certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent H scale M hpred h

/--
[certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent H scale M hpred h

/--
[certificate_rgToExponentBridge_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticBridgeInputs (P.certificate scale M) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_analyticBridgeInputs P scale M h

/--
[certificate_valid_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticBridgeInputs (P.certificate scale M) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_analyticBridgeInputs P scale M h

/--
[certificate_hasCriticalNu_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticBridgeInputs (P.certificate scale M) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_analyticBridgeInputs P scale M h

/--
[certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_valid_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_analyticBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs P scale M h

/--
[certificate_valid_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticPrefactorBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_analyticPrefactorBridgeInputs P scale M h

/--
[certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs P scale M h

/--
[certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_rgToExponentBridge_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticMassBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_analyticMassBridgeInputs P scale M h

/--
[certificate_valid_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticMassBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_analyticMassBridgeInputs P scale M h

/--
[certificate_hasCriticalNu_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticMassBridgeInputs_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_analyticMassBridgeInputs P scale M h

/--
[certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_rgToExponentBridge_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticBridgeInputs (P.certificate scale M) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticBridgeInputs P scale M h

/--
[certificate_valid_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticBridgeInputs (P.certificate scale M) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_analyticBridgeInputs P scale M h

/--
[certificate_hasCriticalNu_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticBridgeInputs (P.certificate scale M) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_analyticBridgeInputs P scale M h

/--
[certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_valid_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_analyticBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs P scale M h

/--
[certificate_valid_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticPrefactorBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_analyticPrefactorBridgeInputs P scale M h

/--
[certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale M) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs P scale M h

/--
[certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_rgToExponentBridge_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticMassBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticMassBridgeInputs P scale M h

/--
[certificate_valid_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticMassBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_analyticMassBridgeInputs P scale M h

/--
[certificate_hasCriticalNu_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticMassBridgeInputs_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (h : RGCertificate.AnalyticMassBridgeInputs (P.certificate scale M) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_analyticMassBridgeInputs P scale M h

/--
[certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent P scale M hpred h

/--
[certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent P scale M hpred h


-- created on 2026-10-23
