import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.IsingTableClosedBallBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingAnalyticTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingAnalyticTarget P scale T

/--
[certificate_rgToExponentBridge_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassAnalyticTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassAnalyticTarget P scale T

/--
[certificate_rgToExponentBridge_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassPowerLawTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassPowerLawTarget P scale T

/--
[certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget P scale T

/--
[certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget P scale T

/--
[certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget P scale T

/--
[certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_freeAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_freeMassAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_freeMassPowerLawToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingAnalyticTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingAnalyticTarget P scale T

/--
[certificate_hasCriticalNu_of_isingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingAnalyticTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingAnalyticTarget P scale T

/--
[certificate_valid_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingAnalyticTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassAnalyticTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingMassAnalyticTarget P scale T

/--
[certificate_hasCriticalNu_of_isingMassAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassAnalyticTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingMassAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassAnalyticTarget P scale T

/--
[certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingMassAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassAnalyticTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassPowerLawTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingMassPowerLawTarget P scale T

/--
[certificate_hasCriticalNu_of_isingMassPowerLawTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassPowerLawTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassPowerLawTarget P scale T

/--
[certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassPowerLawAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassPowerLawTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeAnalyticToPlusTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_freeAnalyticToPlusTarget P scale T

/--
[certificate_hasCriticalNu_of_freeAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FreeAnalyticRGToPlusExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_freeAnalyticToPlusTarget P scale T

/--
[certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_freeAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeAnalyticRGToPlusExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_freeAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassAnalyticToPlusTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_freeMassAnalyticToPlusTarget P scale T

/--
[certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FreeMassAnalyticRGToPlusExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget P scale T

/--
[certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_freeMassAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassAnalyticRGToPlusExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_freeMassAnalyticToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassPowerLawToPlusTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_freeMassPowerLawToPlusTarget P scale T

/--
[certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget P scale T

/--
[certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_freeMassPowerLawToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_freeMassPowerLawToPlusTarget_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs P scale T

/--
[certificate_valid_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingRGCoordinateBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingRGCoordinateBridgeInputs P scale T

/--
[certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingRGCoordinateBridgeInputs (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs P scale T

/--
[certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs P scale T

/--
[certificate_valid_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassRGCoordinateBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  (P.certificate scale).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingMassRGCoordinateBridgeInputs P scale T

/--
[certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {T : IsingMassRGCoordinateBridgeInputs (P.certificate scale)}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs P scale T

/--
[certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  (P.certificate scale).Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T

/--
[certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingTableClosedBallBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs D}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) Ising3DModel n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_isingMassRGCoordinateBridgeInputs_congr_predictedExponent P scale hpred T


-- created on 2026-10-23
