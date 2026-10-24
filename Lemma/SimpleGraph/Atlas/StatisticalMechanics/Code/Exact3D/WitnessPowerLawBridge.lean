import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.WitnessPowerLawBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteWitnessPackage StatMech.Exact3D.InfiniteTailWitnessPackage StatMech.Exact3D.InfiniteTailTableWitnessPackage


/--
[rgToExponentBridge_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_eventually_exact_power_prefactor W correlationLength hA hξ

/--
[valid_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_eventually_exact_power_prefactor W correlationLength hA hξ

/--
[hasCriticalNu_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_eventually_exact_power_prefactor W correlationLength hA hξ

/--
[rgToExponentBridge_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_prefactor_on_Ioo_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_exact_power_prefactor_on_Ioo W correlationLength δ hA hδ hξ

/--
[valid_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_prefactor_on_Ioo_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_exact_power_prefactor_on_Ioo W correlationLength δ hA hδ hξ

/--
[hasCriticalNu_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_prefactor_on_Ioo_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_exact_power_prefactor_on_Ioo W correlationLength δ hA hδ hξ

/--
[rgToExponentBridge_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_variable_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_eventually_exact_power_variable_prefactor W correlationLength A hA hlogA hξ

/--
[valid_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_variable_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_eventually_exact_power_variable_prefactor W correlationLength A hA hlogA hξ

/--
[hasCriticalNu_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_variable_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_eventually_exact_power_variable_prefactor W correlationLength A hA hlogA hξ

/--
[rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo W correlationLength A δ hδ hA hlogA hξ

/--
[valid_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_exact_power_variable_prefactor_on_Ioo W correlationLength A δ hδ hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo W correlationLength A δ hδ hA hlogA hξ

/--
[rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor W correlationLength mass B hB hlogB hmass hξ

/--
[valid_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_mass_power_variable_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_eventually_exact_mass_power_variable_prefactor W correlationLength mass B hB hlogB hmass hξ

/--
[hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor W correlationLength mass B hB hlogB hmass hξ

/--
[rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo W correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[valid_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_exact_mass_power_variable_prefactor_on_Ioo W correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo W correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent W correlationLength δ hpred hA hδ hξ

/--
[valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent W correlationLength δ hpred hA hδ hξ

/--
[hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent W correlationLength δ hpred hA hδ hξ

/--
[rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength A δ hpred hδ hA hlogA hξ

/--
[valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength A δ hpred hδ hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength A δ hpred hδ hA hlogA hξ

/--
[rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent W correlationLength hpred hA hξ

/--
[valid_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_eventually_exact_power_prefactor_congr_predictedExponent W correlationLength hpred hA hξ

/--
[hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent W correlationLength hpred hA hξ

/--
[rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent W correlationLength A hpred hA hlogA hξ

/--
[valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent W correlationLength A hpred hA hlogA hξ

/--
[hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent W correlationLength A hpred hA hlogA hξ

/--
[rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent W correlationLength mass B hpred hB hlogB hmass hξ

/--
[valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent W correlationLength mass B hpred hB hlogB hmass hξ

/--
[hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent W correlationLength mass B hpred hB hlogB hmass hξ

/--
[rgToExponentBridge_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_eventually_exact_power_prefactor W correlationLength hA hξ

/--
[valid_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_eventually_exact_power_prefactor W correlationLength hA hξ

/--
[hasCriticalNu_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_eventually_exact_power_prefactor W correlationLength hA hξ

/--
[rgToExponentBridge_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_exact_power_prefactor_on_Ioo W correlationLength δ hA hδ hξ

/--
[valid_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_exact_power_prefactor_on_Ioo W correlationLength δ hA hδ hξ

/--
[hasCriticalNu_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_exact_power_prefactor_on_Ioo W correlationLength δ hA hδ hξ

/--
[rgToExponentBridge_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_variable_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_eventually_exact_power_variable_prefactor W correlationLength A hA hlogA hξ

/--
[valid_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_variable_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_eventually_exact_power_variable_prefactor W correlationLength A hA hlogA hξ

/--
[hasCriticalNu_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_variable_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_eventually_exact_power_variable_prefactor W correlationLength A hA hlogA hξ

/--
[rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo W correlationLength A δ hδ hA hlogA hξ

/--
[valid_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_exact_power_variable_prefactor_on_Ioo W correlationLength A δ hδ hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo W correlationLength A δ hδ hA hlogA hξ

/--
[rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor W correlationLength mass B hB hlogB hmass hξ

/--
[valid_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_mass_power_variable_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_eventually_exact_mass_power_variable_prefactor W correlationLength mass B hB hlogB hmass hξ

/--
[hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor W correlationLength mass B hB hlogB hmass hξ

/--
[rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo W correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[valid_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_exact_mass_power_variable_prefactor_on_Ioo W correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo W correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent W correlationLength δ hpred hA hδ hξ

/--
[valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent W correlationLength δ hpred hA hδ hξ

/--
[hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent W correlationLength δ hpred hA hδ hξ

/--
[rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength A δ hpred hδ hA hlogA hξ

/--
[valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength A δ hpred hδ hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength A δ hpred hδ hA hlogA hξ

/--
[rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent W correlationLength hpred hA hξ

/--
[valid_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_eventually_exact_power_prefactor_congr_predictedExponent W correlationLength hpred hA hξ

/--
[hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent W correlationLength hpred hA hξ

/--
[rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent W correlationLength A hpred hA hlogA hξ

/--
[valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent W correlationLength A hpred hA hlogA hξ

/--
[hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent W correlationLength A hpred hA hlogA hξ

/--
[rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent W correlationLength mass B hpred hB hlogB hmass hξ

/--
[valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent W correlationLength mass B hpred hB hlogB hmass hξ

/--
[hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent W correlationLength mass B hpred hB hlogB hmass hξ

/--
[rgToExponentBridge_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_eventually_exact_power_prefactor W correlationLength hA hξ

/--
[valid_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_eventually_exact_power_prefactor W correlationLength hA hξ

/--
[hasCriticalNu_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_eventually_exact_power_prefactor W correlationLength hA hξ

/--
[rgToExponentBridge_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_exact_power_prefactor_on_Ioo W correlationLength δ hA hδ hξ

/--
[valid_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_exact_power_prefactor_on_Ioo W correlationLength δ hA hδ hξ

/--
[hasCriticalNu_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_exact_power_prefactor_on_Ioo W correlationLength δ hA hδ hξ

/--
[rgToExponentBridge_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_variable_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_eventually_exact_power_variable_prefactor W correlationLength A hA hlogA hξ

/--
[valid_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_variable_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_eventually_exact_power_variable_prefactor W correlationLength A hA hlogA hξ

/--
[hasCriticalNu_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_variable_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_eventually_exact_power_variable_prefactor W correlationLength A hA hlogA hξ

/--
[rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo W correlationLength A δ hδ hA hlogA hξ

/--
[valid_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_exact_power_variable_prefactor_on_Ioo W correlationLength A δ hδ hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-W.certificate.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo W correlationLength A δ hδ hA hlogA hξ

/--
[rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor W correlationLength mass B hB hlogB hmass hξ

/--
[valid_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_mass_power_variable_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_eventually_exact_mass_power_variable_prefactor W correlationLength mass B hB hlogB hmass hξ

/--
[hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor W correlationLength mass B hB hlogB hmass hξ

/--
[rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo W correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[valid_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_exact_mass_power_variable_prefactor_on_Ioo W correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (W.certificate.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo W correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent W correlationLength δ hpred hA hδ hξ

/--
[valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent W correlationLength δ hpred hA hδ hξ

/--
[hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent W correlationLength δ hpred hA hδ hξ

/--
[rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength A δ hpred hδ hA hlogA hξ

/--
[valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength A δ hpred hδ hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength A δ hpred hδ hA hlogA hξ

/--
[rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent W correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent W correlationLength hpred hA hξ

/--
[valid_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_eventually_exact_power_prefactor_congr_predictedExponent W correlationLength hpred hA hξ

/--
[hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent W correlationLength hpred hA hξ

/--
[rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent W correlationLength A hpred hA hlogA hξ

/--
[valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent W correlationLength A hpred hA hlogA hξ

/--
[hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent W correlationLength A hpred hA hlogA hξ

/--
[rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent W correlationLength mass B hpred hB hlogB hmass hξ

/--
[valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent W correlationLength mass B hpred hB hlogB hmass hξ

/--
[hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/WitnessPowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent W correlationLength mass B hpred hB hlogB hmass hξ


-- created on 2026-10-23
