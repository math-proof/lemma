import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.FKTableClosedBallBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fkTarget P scale T

/--
[certificate_valid_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fkTarget P scale T

/--
[certificate_hasCriticalNu_of_fkTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKToIsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fkTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fkTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fkTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKToIsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fkTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkPowerLawTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fkPowerLawTarget P scale T

/--
[certificate_valid_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkPowerLawTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fkPowerLawTarget P scale T

/--
[certificate_hasCriticalNu_of_fkPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkPowerLawTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fkPowerLawTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fkPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkPowerLawTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fkPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fkPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fkMassTarget P scale T

/--
[certificate_valid_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fkMassTarget P scale T

/--
[certificate_hasCriticalNu_of_fkMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKMassAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fkMassTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fkMassTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fkMassTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fkMassTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassPowerLawTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fkMassPowerLawTarget P scale T

/--
[certificate_valid_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassPowerLawTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fkMassPowerLawTarget P scale T

/--
[certificate_hasCriticalNu_of_fkMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassPowerLawTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fkMassPowerLawTarget P scale T

/--
[certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fkMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fkMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fkMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (P.certificate scale).predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq P scale hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (P.certificate scale).predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fk_pOfBeta_eventually_eq P scale hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength (P.certificate scale).predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq P scale hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_pOfBeta_eventually_eq_congr_predictedExponent P scale hpred hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fk_pOfBeta_eventually_eq_congr_predictedExponent P scale hpred hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hfk : HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) fkCorrelationLength D.predictedExponent)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fk_pOfBeta_eventually_eq_congr_predictedExponent P scale hpred hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hfk : ((P.certificate scale).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_pOfBeta_rgToExponentBridge_eventually_eq P scale hfk hEq

/--
[certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hfk : ((P.certificate scale).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fk_pOfBeta_rgToExponentBridge_eventually_eq P scale hfk hEq

/--
[certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hfk : ((P.certificate scale).retarget (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))).RGToExponentBridge fkCorrelationLength)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fk_pOfBeta_rgToExponentBridge_eventually_eq P scale hfk hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(P.certificate scale).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_exact_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(P.certificate scale).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fk_exact_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-(P.certificate scale).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fk_exact_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkPrefactor pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[certificate_rgBridge_of_fk_power_Ioo_congr_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgBridge_of_fk_power_Ioo_congr_exp_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgBridge_of_fk_power_Ioo_congr_exp P scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[certificate_valid_of_fk_power_Ioo_congr_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_power_Ioo_congr_exp_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fk_power_Ioo_congr_exp P scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[certificate_hasNu_of_fk_power_Ioo_congr_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasNu_of_fk_power_Ioo_congr_exp_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hscaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = fkPrefactor p * Real.exp (-D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasNu_of_fk_power_Ioo_congr_exp P scale isingCorrelationLength fkCorrelationLength fkPrefactor hpred pδ hpδ hpref_pos hlogpref hscaling hEq

/--
[certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((P.certificate scale).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((P.certificate scale).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fk_exact_mass_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp ((P.certificate scale).predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_fk_exact_mass_power_variable_prefactor_on_Ioo P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_rgBridge_of_fk_mass_Ioo_congr_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgBridge_of_fk_mass_Ioo_congr_exp_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).RGToExponentBridge isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgBridge_of_fk_mass_Ioo_congr_exp P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_valid_of_fk_mass_Ioo_congr_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_fk_mass_Ioo_congr_exp_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  (P.certificate scale).Valid isingCorrelationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_fk_mass_Ioo_congr_exp P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq

/--
[certificate_hasNu_of_fk_mass_Ioo_congr_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasNu_of_fk_mass_Ioo_congr_exp_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor : ℝ → ℝ}
  {pδ : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hpδ : 0 < pδ)
  (hpref_pos : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → 0 < fkMassPrefactor p)
  (hlogpref : Filter.Tendsto (fun p : ℝ => Real.log (fkMassPrefactor p) / Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)) (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3)) (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0))
  (hmass_scaling : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkMass p = fkMassPrefactor p * Real.exp (D.predictedExponent * Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p)))
  (hfk_length_eq_inv_mass : ∀ p, p ∈ Set.Ioo (IsingFK.pOfBeta (Ising.betaC 3) - pδ) (IsingFK.pOfBeta (Ising.betaC 3)) → fkCorrelationLength p = (fkMass p)⁻¹)
  (hEq : ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel isingCorrelationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasNu_of_fk_mass_Ioo_congr_exp P scale isingCorrelationLength fkCorrelationLength fkMass fkMassPrefactor hpred pδ hpδ hpref_pos hlogpref hmass_scaling hfk_length_eq_inv_mass hEq


-- created on 2026-10-23
