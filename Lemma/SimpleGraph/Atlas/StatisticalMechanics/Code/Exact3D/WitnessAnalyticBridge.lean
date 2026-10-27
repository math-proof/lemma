import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.WitnessAnalyticBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteWitnessPackage StatMech.Exact3D.InfiniteTailWitnessPackage StatMech.Exact3D.InfiniteTailTableWitnessPackage


/--
[rgToExponentBridge_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticBridgeInputs_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticBridgeInputs W.certificate correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_analyticBridgeInputs W h

/--
[valid_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticBridgeInputs_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticBridgeInputs W.certificate correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_analyticBridgeInputs W h

/--
[hasCriticalNu_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticBridgeInputs_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticBridgeInputs W.certificate correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_analyticBridgeInputs W h

/--
[rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent W hpred h

/--
[valid_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_analyticBridgeInputs_congr_predictedExponent W hpred h

/--
[hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent W hpred h

/--
[rgToExponentBridge_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticPrefactorBridgeInputs_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs W.certificate correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_analyticPrefactorBridgeInputs W h

/--
[valid_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticPrefactorBridgeInputs_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs W.certificate correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_analyticPrefactorBridgeInputs W h

/--
[hasCriticalNu_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticPrefactorBridgeInputs_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs W.certificate correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_analyticPrefactorBridgeInputs W h

/--
[rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent W hpred h

/--
[valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent W hpred h

/--
[hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent W hpred h

/--
[rgToExponentBridge_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticMassBridgeInputs_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticMassBridgeInputs W.certificate correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_analyticMassBridgeInputs W h

/--
[valid_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticMassBridgeInputs_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticMassBridgeInputs W.certificate correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_analyticMassBridgeInputs W h

/--
[hasCriticalNu_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticMassBridgeInputs_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticMassBridgeInputs W.certificate correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_analyticMassBridgeInputs W h

/--
[rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent W hpred h

/--
[valid_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticMassBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_analyticMassBridgeInputs_congr_predictedExponent W hpred h

/--
[hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent W hpred h

/--
[rgToExponentBridge_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticBridgeInputs_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticBridgeInputs W.certificate correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_analyticBridgeInputs W h

/--
[valid_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticBridgeInputs_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticBridgeInputs W.certificate correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_analyticBridgeInputs W h

/--
[hasCriticalNu_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticBridgeInputs_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticBridgeInputs W.certificate correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_analyticBridgeInputs W h

/--
[rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent W hpred h

/--
[valid_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_analyticBridgeInputs_congr_predictedExponent W hpred h

/--
[hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent W hpred h

/--
[rgToExponentBridge_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticPrefactorBridgeInputs_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs W.certificate correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_analyticPrefactorBridgeInputs W h

/--
[valid_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticPrefactorBridgeInputs_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs W.certificate correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_analyticPrefactorBridgeInputs W h

/--
[hasCriticalNu_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticPrefactorBridgeInputs_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs W.certificate correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_analyticPrefactorBridgeInputs W h

/--
[rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent W hpred h

/--
[valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent W hpred h

/--
[hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent W hpred h

/--
[rgToExponentBridge_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticMassBridgeInputs_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticMassBridgeInputs W.certificate correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_analyticMassBridgeInputs W h

/--
[valid_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticMassBridgeInputs_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticMassBridgeInputs W.certificate correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_analyticMassBridgeInputs W h

/--
[hasCriticalNu_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticMassBridgeInputs_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (h : RGCertificate.AnalyticMassBridgeInputs W.certificate correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_analyticMassBridgeInputs W h

/--
[rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent W hpred h

/--
[valid_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticMassBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_analyticMassBridgeInputs_congr_predictedExponent W hpred h

/--
[hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent W hpred h

/--
[rgToExponentBridge_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (h : RGCertificate.AnalyticBridgeInputs W.certificate correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_analyticBridgeInputs W h

/--
[valid_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (h : RGCertificate.AnalyticBridgeInputs W.certificate correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_analyticBridgeInputs W h

/--
[hasCriticalNu_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (h : RGCertificate.AnalyticBridgeInputs W.certificate correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_analyticBridgeInputs W h

/--
[rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent W hpred h

/--
[valid_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_analyticBridgeInputs_congr_predictedExponent W hpred h

/--
[hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent W hpred h

/--
[rgToExponentBridge_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticPrefactorBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs W.certificate correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_analyticPrefactorBridgeInputs W h

/--
[valid_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticPrefactorBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs W.certificate correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_analyticPrefactorBridgeInputs W h

/--
[hasCriticalNu_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticPrefactorBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs W.certificate correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_analyticPrefactorBridgeInputs W h

/--
[rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent W hpred h

/--
[valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent W hpred h

/--
[hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent W hpred h

/--
[rgToExponentBridge_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticMassBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (h : RGCertificate.AnalyticMassBridgeInputs W.certificate correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_analyticMassBridgeInputs W h

/--
[valid_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticMassBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (h : RGCertificate.AnalyticMassBridgeInputs W.certificate correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_analyticMassBridgeInputs W h

/--
[hasCriticalNu_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticMassBridgeInputs_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (h : RGCertificate.AnalyticMassBridgeInputs W.certificate correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_analyticMassBridgeInputs W h

/--
[rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent W hpred h

/--
[valid_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma valid_of_analyticMassBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_analyticMassBridgeInputs_congr_predictedExponent W hpred h

/--
[hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessAnalyticBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent W hpred h


-- created on 2026-10-23
