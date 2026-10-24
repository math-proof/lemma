import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.TableClosedBallReparameterizationBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hν : HasCriticalNu N correlationLength (P.certificate scale).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq P scale hν hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent P scale hpred hν hφ hEq

/--
[certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent P scale hpred hν hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : D.predictedExponent = (P.certificate scale).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq P scale D hpred hbridge hφ hEq

/--
[certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent P scale D hpred hbridge hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : ((P.certificate scale).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq P scale hbridge hφ hEq

/--
[certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hν : HasCriticalNu N correlationLength (P.certificate scale).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq P scale hν hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hν : HasCriticalNu N correlationLength (P.certificate scale).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq P scale hν hφ hEq

/--
[certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent P scale hpred hν hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent P scale hpred hν hφ hEq

/--
[certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : D.predictedExponent = (P.certificate scale).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq P scale D hpred hbridge hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : D.predictedExponent = (P.certificate scale).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq P scale D hpred hbridge hφ hEq

/--
[certificate_valid_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_retargetBridge_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : ((P.certificate scale).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_reparameterized_retargetBridge_eventually_eq P scale hbridge hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TableClosedBallReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : ((P.certificate scale).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq P scale hbridge hφ hEq


-- created on 2026-10-23
