import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailReparameterizationBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailHyperbolicSplitting StatMech.Exact3D.FinitePlusTailBlockRGPackage StatMech.Exact3D.FinitePlusTailClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength (H.certificate scale M).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq H scale hν hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent H scale hpred hν hφ hEq

/--
[certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent H scale hpred hν hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = (H.certificate scale M).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq H scale D hpred hbridge hφ hEq

/--
[certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent H scale D hpred hbridge hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : ((H.certificate scale M).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq H scale hbridge hφ hEq

/--
[certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength (H.certificate scale M).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq H scale hν hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength (H.certificate scale M).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq H scale hν hφ hEq

/--
[certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent H scale hpred hν hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent H scale hpred hν hφ hEq

/--
[certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = (H.certificate scale M).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq H scale D hpred hbridge hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = (H.certificate scale M).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq H scale D hpred hbridge hφ hEq

/--
[certificate_valid_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_retargetBridge_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : ((H.certificate scale M).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (H.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_reparameterized_retargetBridge_eventually_eq H scale hbridge hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : ((H.certificate scale M).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq H scale hbridge hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength (P.certificate scale M).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq P scale hν hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent P scale hpred hν hφ hEq

/--
[certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent P scale hpred hν hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq P scale D hpred hbridge hφ hEq

/--
[certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent P scale D hpred hbridge hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq P scale hbridge hφ hEq

/--
[certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength (P.certificate scale M).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq P scale hν hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength (P.certificate scale M).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq P scale hν hφ hEq

/--
[certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent P scale hpred hν hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent P scale hpred hν hφ hEq

/--
[certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq P scale D hpred hbridge hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq P scale D hpred hbridge hφ hEq

/--
[certificate_valid_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_retargetBridge_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_reparameterized_retargetBridge_eventually_eq P scale hbridge hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq P scale hbridge hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength (P.certificate scale M).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq P scale hν hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_reparameterized_hasCriticalNu_congrExponent P scale hpred hν hφ hEq

/--
[certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_bridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent P scale hpred hν hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq P scale D hpred hbridge hφ hEq

/--
[certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_bridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent P scale D hpred hbridge hφ hEq

/--
[certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq P scale hbridge hφ hEq

/--
[certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength (P.certificate scale M).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq P scale hν hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength (P.certificate scale M).predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq P scale hν hφ hEq

/--
[certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent P scale hpred hν hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent P scale hpred hν hφ hEq

/--
[certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_reparameterized_rgToExponentBridge_eventually_eq P scale D hpred hbridge hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = (P.certificate scale M).predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq P scale D hpred hbridge hφ hEq

/--
[certificate_valid_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_valid_of_reparameterized_retargetBridge_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_reparameterized_retargetBridge_eventually_eq P scale hbridge hφ hEq

/--
[certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailReparameterizationBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : ((P.certificate scale M).retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq P scale hbridge hφ hEq


-- created on 2026-10-23
