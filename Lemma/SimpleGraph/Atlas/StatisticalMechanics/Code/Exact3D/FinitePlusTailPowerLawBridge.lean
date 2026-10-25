import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailPowerLawBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FinitePlusTailHyperbolicSplitting StatMech.Exact3D.FinitePlusTailBlockRGPackage StatMech.Exact3D.FinitePlusTailClosedBallRGPackage


/--
[certificate_rgToExponentBridge_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor H scale M correlationLength hA hξ

/--
[certificate_valid_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_eventually_exact_power_prefactor H scale M correlationLength hA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_exact_power_prefactor H scale M correlationLength hA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo H scale M correlationLength δ hA hδ hξ

/--
[certificate_valid_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_exact_power_prefactor_on_Ioo H scale M correlationLength δ hA hδ hξ

/--
[certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo H scale M correlationLength δ hA hδ hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor H scale M correlationLength A hA hlogA hξ

/--
[certificate_valid_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_variable_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_eventually_exact_power_variable_prefactor H scale M correlationLength A hA hlogA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor H scale M correlationLength A hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo H scale M correlationLength A δ hδ hA hlogA hξ

/--
[certificate_valid_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_exact_power_variable_prefactor_on_Ioo H scale M correlationLength A δ hδ hA hlogA hξ

/--
[certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(H.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo H scale M correlationLength A δ hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor H scale M correlationLength mass B hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_eventually_exact_mass_power_variable_prefactor H scale M correlationLength mass B hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor H scale M correlationLength mass B hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo H scale M correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo H scale M correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((H.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo H scale M correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent H scale M correlationLength δ hpred hA hδ hξ

/--
[certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent H scale M correlationLength δ hpred hA hδ hξ

/--
[certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent H scale M correlationLength δ hpred hA hδ hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred H scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred H scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred H scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred H scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred H scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred H scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent H scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent H scale M correlationLength hpred hA hξ

/--
[certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent H scale M correlationLength hpred hA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent H scale M correlationLength hpred hA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred H scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent H scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent H scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent H scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred H scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent H scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred H scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred H scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (H.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent H scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent H scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor P scale M correlationLength hA hξ

/--
[certificate_valid_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_eventually_exact_power_prefactor P scale M correlationLength hA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor P scale M correlationLength hA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo P scale M correlationLength δ hA hδ hξ

/--
[certificate_valid_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_exact_power_prefactor_on_Ioo P scale M correlationLength δ hA hδ hξ

/--
[certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo P scale M correlationLength δ hA hδ hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor P scale M correlationLength A hA hlogA hξ

/--
[certificate_valid_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_variable_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_eventually_exact_power_variable_prefactor P scale M correlationLength A hA hlogA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor P scale M correlationLength A hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo P scale M correlationLength A δ hδ hA hlogA hξ

/--
[certificate_valid_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_exact_power_variable_prefactor_on_Ioo P scale M correlationLength A δ hδ hA hlogA hξ

/--
[certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo P scale M correlationLength A δ hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor P scale M correlationLength mass B hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_eventually_exact_mass_power_variable_prefactor P scale M correlationLength mass B hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor P scale M correlationLength mass B hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo P scale M correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo P scale M correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo P scale M correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength δ hpred hA hδ hξ

/--
[certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength δ hpred hA hδ hξ

/--
[certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength δ hpred hA hδ hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent P scale M correlationLength hpred hA hξ

/--
[certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent P scale M correlationLength hpred hA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent P scale M correlationLength hpred hA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred P scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent P scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent P scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent P scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor P scale M correlationLength hA hξ

/--
[certificate_valid_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_exact_power_prefactor P scale M correlationLength hA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor P scale M correlationLength hA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo P scale M correlationLength δ hA hδ hξ

/--
[certificate_valid_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_exact_power_prefactor_on_Ioo P scale M correlationLength δ hA hδ hξ

/--
[certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo P scale M correlationLength δ hA hδ hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor P scale M correlationLength A hA hlogA hξ

/--
[certificate_valid_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_variable_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_exact_power_variable_prefactor P scale M correlationLength A hA hlogA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor P scale M correlationLength A hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo P scale M correlationLength A δ hδ hA hlogA hξ

/--
[certificate_valid_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_exact_power_variable_prefactor_on_Ioo P scale M correlationLength A δ hδ hA hlogA hξ

/--
[certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-(P.certificate scale M).predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo P scale M correlationLength A δ hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor P scale M correlationLength mass B hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_exact_mass_power_variable_prefactor P scale M correlationLength mass B hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor P scale M correlationLength mass B hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo P scale M correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo P scale M correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp ((P.certificate scale M).predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo P scale M correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength δ hpred hA hδ hξ

/--
[certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength δ hpred hA hδ hξ

/--
[certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength δ hpred hA hδ hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength A δ hpred hδ hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent P scale M correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent P scale M correlationLength hpred hA hξ

/--
[certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_exact_power_prefactor_congr_predictedExponent P scale M correlationLength hpred hA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent P scale M correlationLength hpred hA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_pred P scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent P scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent P scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent P scale M correlationLength A hpred hA hlogA hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_pred P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_pred P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_pred P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  (P.certificate scale M).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent P scale M correlationLength mass B hpred hB hlogB hmass hξ

/--
[certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailPowerLawBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent P scale M correlationLength mass B hpred hB hlogB hmass hξ


-- created on 2026-10-23
