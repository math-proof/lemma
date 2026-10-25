import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.TableClosedBallAnalyticBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (h : RGCertificate.AnalyticBridgeInputs (P.certificate scale) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticBridgeInputs P scale h

/--
[certificate_valid_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (h : RGCertificate.AnalyticBridgeInputs (P.certificate scale) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_analyticBridgeInputs P scale h

/--
[certificate_hasCriticalNu_of_analyticBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (h : RGCertificate.AnalyticBridgeInputs (P.certificate scale) correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_analyticBridgeInputs P scale h

/--
[certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticBridgeInputs_congr_predictedExponent P scale hpred h

/--
[certificate_valid_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_analyticBridgeInputs_congr_predictedExponent P scale hpred h

/--
[certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_analyticBridgeInputs_congr_predictedExponent P scale hpred h

/--
[certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs P scale h

/--
[certificate_valid_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticPrefactorBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_analyticPrefactorBridgeInputs P scale h

/--
[certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs (P.certificate scale) correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs P scale h

/--
[certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticPrefactorBridgeInputs_congr_predictedExponent P scale hpred h

/--
[certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_analyticPrefactorBridgeInputs_congr_predictedExponent P scale hpred h

/--
[certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_analyticPrefactorBridgeInputs_congr_predictedExponent P scale hpred h

/--
[certificate_rgToExponentBridge_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticMassBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (h : RGCertificate.AnalyticMassBridgeInputs (P.certificate scale) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticMassBridgeInputs P scale h

/--
[certificate_valid_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticMassBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (h : RGCertificate.AnalyticMassBridgeInputs (P.certificate scale) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_analyticMassBridgeInputs P scale h

/--
[certificate_hasCriticalNu_of_analyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticMassBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (h : RGCertificate.AnalyticMassBridgeInputs (P.certificate scale) correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_analyticMassBridgeInputs P scale h

/--
[certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_analyticMassBridgeInputs_congr_predictedExponent P scale hpred h

/--
[certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_analyticMassBridgeInputs_congr_predictedExponent P scale hpred h

/--
[certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallAnalyticBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (h : RGCertificate.AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_analyticMassBridgeInputs_congr_predictedExponent P scale hpred h


-- created on 2026-10-23
