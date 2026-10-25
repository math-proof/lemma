import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.WitnessReparameterizationBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteWitnessPackage StatMech.Exact3D.InfiniteTailWitnessPackage StatMech.Exact3D.InfiniteTailTableWitnessPackage


/--
[rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hν : HasCriticalNu N correlationLength W.certificate.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq W hν hφ hEq

/--
[rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent W hpred hν hφ hEq

/--
[rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : D.predictedExponent = W.certificate.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq W D hpred hbridge hφ hEq

/--
[rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : (W.certificate.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq W hbridge hφ hEq

/--
[valid_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_hasCriticalNu_eventually_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hν : HasCriticalNu N correlationLength W.certificate.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq W hν hφ hEq

/--
[hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hν : HasCriticalNu N correlationLength W.certificate.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq W hν hφ hEq

/--
[valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent W hpred hν hφ hEq

/--
[hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent W hpred hν hφ hEq

/--
[valid_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : D.predictedExponent = W.certificate.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_reparameterized_rgToExponentBridge_eventually_eq W D hpred hbridge hφ hEq

/--
[hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : D.predictedExponent = W.certificate.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq W D hpred hbridge hφ hEq

/--
[valid_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_retargetBridge_eventually_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : (W.certificate.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_reparameterized_retargetBridge_eventually_eq W hbridge hφ hEq

/--
[hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : (W.certificate.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq W hbridge hφ hEq

/--
[rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hν : HasCriticalNu N correlationLength W.certificate.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq W hν hφ hEq

/--
[rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent W hpred hν hφ hEq

/--
[rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : D.predictedExponent = W.certificate.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq W D hpred hbridge hφ hEq

/--
[rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : (W.certificate.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq W hbridge hφ hEq

/--
[valid_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_hasCriticalNu_eventually_eq_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hν : HasCriticalNu N correlationLength W.certificate.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq W hν hφ hEq

/--
[hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hν : HasCriticalNu N correlationLength W.certificate.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq W hν hφ hEq

/--
[valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent W hpred hν hφ hEq

/--
[hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent W hpred hν hφ hEq

/--
[valid_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_rgToExponentBridge_eventually_eq_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : D.predictedExponent = W.certificate.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_reparameterized_rgToExponentBridge_eventually_eq W D hpred hbridge hφ hEq

/--
[hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : D.predictedExponent = W.certificate.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq W D hpred hbridge hφ hEq

/--
[valid_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_retargetBridge_eventually_eq_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : (W.certificate.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_reparameterized_retargetBridge_eventually_eq W hbridge hφ hEq

/--
[hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : (W.certificate.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq W hbridge hφ hEq

/--
[rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hν : HasCriticalNu N correlationLength W.certificate.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq W hν hφ hEq

/--
[rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent W hpred hν hφ hEq

/--
[rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : D.predictedExponent = W.certificate.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq W D hpred hbridge hφ hEq

/--
[rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : (W.certificate.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq W hbridge hφ hEq

/--
[valid_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_hasCriticalNu_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hν : HasCriticalNu N correlationLength W.certificate.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq W hν hφ hEq

/--
[hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hν : HasCriticalNu N correlationLength W.certificate.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq W hν hφ hEq

/--
[valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent W hpred hν hφ hEq

/--
[hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent W hpred hν hφ hEq

/--
[valid_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_rgToExponentBridge_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : D.predictedExponent = W.certificate.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_reparameterized_rgToExponentBridge_eventually_eq W D hpred hbridge hφ hEq

/--
[hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : D.predictedExponent = W.certificate.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq W D hpred hbridge hφ hEq

/--
[valid_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma valid_of_reparameterized_retargetBridge_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : (W.certificate.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_reparameterized_retargetBridge_eventually_eq W hbridge hφ hEq

/--
[hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessReparameterizationBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : (W.certificate.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq W hbridge hφ hEq


-- created on 2026-10-23
