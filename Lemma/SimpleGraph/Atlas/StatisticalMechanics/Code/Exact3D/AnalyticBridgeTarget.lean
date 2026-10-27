import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
open StatMech StatMech.Exact3D StatMech.Exact3D.RGCertificate StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs


/--
[eventually_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_exact_power_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.eventually_exact_power h

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.rgToExponentBridge h

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge)
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.valid_of_checks h hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.hasCriticalNu h

/--
[of_eventually_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma of_eventually_exact_power_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  AnalyticBridgeInputs C correlationLength True True True True where rgCovariance := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.of_eventually_exact_power hξ

/--
[of_eventually_exact_power_with_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma of_eventually_exact_power_with_inputs_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (hRG : RGCovariance)
  (hstable : StableManifoldControl)
  (horbit : MicroscopicOrbitEntry)
  (hmass : SubcriticalMassBridge)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where rgCovariance := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.of_eventually_exact_power_with_inputs hRG hstable horbit hmass hξ

/--
[congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  AnalyticBridgeInputs D correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where rgCovariance := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.congr_predictedExponent hpred h

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  D.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.rgToExponentBridge_congr_predictedExponent hpred h

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.valid_of_checks_congr_predictedExponent hpred h hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticBridgeInputs C correlationLength RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticBridgeInputs.hasCriticalNu_congr_predictedExponent hpred h

/--
[eventually_prefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_prefactor_pos_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < prefactor β := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.eventually_prefactor_pos h

/--
[eventually_prefactor_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_prefactor_power_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = prefactor β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.eventually_prefactor_power h

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.rgToExponentBridge h

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge)
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.valid_of_checks h hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.hasCriticalNu h

/--
[of_eventually_prefactor_power_with_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma of_eventually_prefactor_power_with_inputs_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (hRG : RGCovariance)
  (hstable : StableManifoldControl)
  (horbit : MicroscopicOrbitEntry)
  (hmass : SubcriticalMassBridge)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < prefactor β)
  (hlog : Filter.Tendsto (fun β : ℝ => Real.log (prefactor β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = prefactor β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where rgCovariance := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.of_eventually_prefactor_power_with_inputs hRG hstable horbit hmass hpos hlog hξ

/--
[congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where rgCovariance := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.congr_predictedExponent hpred h

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  D.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.rgToExponentBridge_congr_predictedExponent hpred h

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.valid_of_checks_congr_predictedExponent hpred h hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength prefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticPrefactorBridgeInputs.hasCriticalNu_congr_predictedExponent hpred h

/--
[eventually_massPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_massPrefactor_pos_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < massPrefactor β := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.eventually_massPrefactor_pos h

/--
[eventually_mass_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_mass_power_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = massPrefactor β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)) := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.eventually_mass_power h

/--
[eventually_correlationLength_eq_inv_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_inv_mass_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹ := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.eventually_correlationLength_eq_inv_mass h

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_3
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.rgToExponentBridge h

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_eq_3
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge)
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.valid_of_checks h hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_eq_3
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.hasCriticalNu h

/--
[of_eventually_mass_power_with_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma of_eventually_mass_power_with_inputs_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
-- given
  (hRG : RGCovariance)
  (hstable : StableManifoldControl)
  (horbit : MicroscopicOrbitEntry)
  (hmassBridge : SubcriticalMassBridge)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < massPrefactor β)
  (hlog : Filter.Tendsto (fun β : ℝ => Real.log (massPrefactor β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = massPrefactor β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where rgCovariance := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.of_eventually_mass_power_with_inputs hRG hstable horbit hmassBridge hpos hlog hmass hξ

/--
[congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma congr_predictedExponent_eq_3
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  AnalyticMassBridgeInputs D correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where rgCovariance := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.congr_predictedExponent hpred h

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_3
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  D.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.rgToExponentBridge_congr_predictedExponent hpred h

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_3
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.valid_of_checks_congr_predictedExponent hpred h hfinite htail hfixed hlinear hhyperbolic horbit

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_3
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass massPrefactor : ℝ → ℝ}
  {RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge : Prop}
  {D : RGCertificate M}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (h : AnalyticMassBridgeInputs C correlationLength mass massPrefactor RGCovariance StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
-- imply
  HasCriticalNu M correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.AnalyticMassBridgeInputs.hasCriticalNu_congr_predictedExponent hpred h


-- created on 2026-10-23
