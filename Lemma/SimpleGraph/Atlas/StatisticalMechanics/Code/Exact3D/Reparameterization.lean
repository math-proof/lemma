import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
open StatMech StatMech.Exact3D StatMech.Exact3D.LeftCriticalReparam StatMech.Exact3D.RGCertificate


/--
[id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma id_eq
  {M : CriticalModel ι} :
-- imply
  LeftCriticalReparam M M id where tendsto_left := by
-- proof
  apply StatMech.Exact3D.LeftCriticalReparam.id M

/--
[linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma linear_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {a : ℝ}
-- given
  (ha : 0 < a) :
-- imply
  LeftCriticalReparam M N (linearMap M N a) where tendsto_left := by
-- proof
  apply StatMech.Exact3D.LeftCriticalReparam.linear M N ha

/--
[eventually_comp_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma eventually_comp_left_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {φ : ℝ → ℝ}
  {P : ℝ → Prop}
-- given
  (hφ : LeftCriticalReparam M N φ)
  (hP : ∀ᶠ γ in nhdsWithin N.betaC (Set.Iio N.betaC), P γ) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), P (φ β) := by
-- proof
  apply StatMech.Exact3D.LeftCriticalReparam.eventually_comp_left hφ hP

/--
[eventually_eq_comp_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma eventually_eq_comp_left_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {φ f g : ℝ → ℝ}
-- given
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ γ in nhdsWithin N.betaC (Set.Iio N.betaC), f γ = g γ) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), f (φ β) = g (φ β) := by
-- proof
  apply StatMech.Exact3D.LeftCriticalReparam.eventually_eq_comp_left hφ hEq

/--
[HasCriticalNu.comp_leftCriticalReparam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma comp_leftCriticalReparam_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ) :
-- imply
  HasCriticalNu M (fun β => correlationLength (φ β)) ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.comp_leftCriticalReparam hν hφ

/--
[HasCriticalNu.comp_leftCriticalReparam_congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma comp_leftCriticalReparam_congr_eventually_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.comp_leftCriticalReparam_congr_eventually hν hφ hEq

/--
[rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength C.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  C.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq C hν hφ hEq

/--
[rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : C.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  C.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent C hpred hν hφ hEq

/--
[rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  C.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq C D hpred hbridge hφ hEq

/--
[rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  C.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_reparameterized_rgToExponentBridge_eventually_eq_congr_predictedExponent C D hpred hbridge hφ hEq

/--
[rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : (C.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  C.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_reparameterized_retargetBridge_eventually_eq C hbridge hφ hEq

/--
[valid_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma valid_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_reparameterized_rgToExponentBridge_eventually_eq C D hpred hbridge hφ hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma valid_of_reparameterized_retargetBridge_eventually_eq_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : (C.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_reparameterized_retargetBridge_eventually_eq C hbridge hφ hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma valid_of_reparameterized_hasCriticalNu_eventually_eq_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength C.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_reparameterized_hasCriticalNu_eventually_eq C hν hφ hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : C.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent C hpred hν hφ hEq hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {D : RGCertificate N}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_reparameterized_rgToExponentBridge_eventually_eq C D hpred hbridge hφ hEq

/--
[hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hbridge : (C.retarget N).RGToExponentBridge correlationLength)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_reparameterized_retargetBridge_eventually_eq C hbridge hφ hEq

/--
[hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength C.predictedExponent)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq C hν hφ hEq

/--
[hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean)
-/
@[path]
private lemma hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {φ : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hpred : C.predictedExponent = ν)
  (hν : HasCriticalNu N correlationLength ν)
  (hφ : LeftCriticalReparam M N φ)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength (φ β)) :
-- imply
  HasCriticalNu M comparisonLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_reparameterized_hasCriticalNu_eventually_eq_congr_predictedExponent C hpred hν hφ hEq


-- created on 2026-10-23
