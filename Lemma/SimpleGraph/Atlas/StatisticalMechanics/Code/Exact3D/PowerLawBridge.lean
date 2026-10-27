import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.RGCertificate


/--
[tendsto_betaC_sub_nhdsWithin_Iio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma tendsto_betaC_sub_nhdsWithin_Iio_eq
  {M : CriticalModel ι} :
-- imply
  Filter.Tendsto (fun β : ℝ => M.betaC - β) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhdsWithin 0 (Set.Ioi 0)) := by
-- proof
  apply StatMech.Exact3D.tendsto_betaC_sub_nhdsWithin_Iio M

/--
[tendsto_log_betaC_sub_atBot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma tendsto_log_betaC_sub_atBot_eq
  {M : CriticalModel ι} :
-- imply
  Filter.Tendsto (fun β : ℝ => Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) Filter.atBot := by
-- proof
  apply StatMech.Exact3D.tendsto_log_betaC_sub_atBot M

/--
[logSlope_eq_of_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma logSlope_eq_of_exact_power_prefactor_eq
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A ν β : ℝ}
-- given
  (hA : 0 < A)
  (hβ : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1)
  (hξ : correlationLength β = A * Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  logSlope M correlationLength β = ν - Real.log A / Real.log (M.betaC - β) := by
-- proof
  apply StatMech.Exact3D.logSlope_eq_of_exact_power_prefactor M correlationLength A ν β hA hβ hξ

/--
[logSlope_eq_of_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma logSlope_eq_of_exact_power_variable_prefactor_eq
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {ν β : ℝ}
-- given
  (hA : 0 < A β)
  (hβ : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1)
  (hξ : correlationLength β = A β * Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  logSlope M correlationLength β = ν - Real.log (A β) / Real.log (M.betaC - β) := by
-- proof
  apply StatMech.Exact3D.logSlope_eq_of_exact_power_variable_prefactor M correlationLength A ν β hA hβ hξ

/--
[hasCriticalNu_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_prefactor_eq
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A ν : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_eventually_exact_power_prefactor M correlationLength hA hξ

/--
[hasCriticalNu_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_prefactor_on_Ioo_eq
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {A ν : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_exact_power_prefactor_on_Ioo M correlationLength δ hA hδ hξ

/--
[hasCriticalNu_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_variable_prefactor_eq
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_eventually_exact_power_variable_prefactor M correlationLength A ν hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_eq
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {ν δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo M correlationLength A ν δ hδ hA hlogA hξ

/--
[tendsto_log_inv_prefactor_div_log_betaC_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma tendsto_log_inv_prefactor_div_log_betaC_sub_eq
  {M : CriticalModel ι}
  {A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  Filter.Tendsto (fun β : ℝ => Real.log ((A β)⁻¹) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_log_inv_prefactor_div_log_betaC_sub M hA hlogA

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {ν δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (ν * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo M correlationLength mass B ν δ hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_eq
  {M : CriticalModel ι}
  {correlationLength mass B : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (ν * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor M correlationLength mass B ν hB hlogB hmass hξ

/--
[HasCriticalNu.mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma mul_log_negligible_prefactor_eq
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
  {ν : ℝ}
-- given
  (hν : HasCriticalNu M correlationLength ν)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.mul_log_negligible_prefactor hν hξpos hApos hlogA

/--
[HasCriticalNu.const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma const_mul_eq
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {ν A : ℝ}
-- given
  (hν : HasCriticalNu M correlationLength ν)
  (hA : 0 < A)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β) :
-- imply
  HasCriticalNu M (fun β => A * correlationLength β) ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.const_mul hν hA hξpos

/--
[tendsto_log_bounded_prefactor_div_log_betaC_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma tendsto_log_bounded_prefactor_div_log_betaC_sub_eq
  {M : CriticalModel ι}
  {A : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hcLo : 0 < cLo)
  (_hcHi : 0 < cHi)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo ≤ A β ∧ A β ≤ cHi) :
-- imply
  Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0) := by
-- proof
  apply StatMech.Exact3D.tendsto_log_bounded_prefactor_div_log_betaC_sub M hcLo _hcHi hA

/--
[HasCriticalNu.of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma of_eventually_const_mul_le_le_eq
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {ν cLo cHi : ℝ}
-- given
  (hν : HasCriticalNu M correlationLength ν)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength ν := by
-- proof
  apply StatMech.Exact3D.HasCriticalNu.of_eventually_const_mul_le_le hν hξpos hcLo hcHi hcompare

/--
[hasCriticalNu_of_eventually_const_mul_exact_power_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_exact_power_le_le_eq
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {ν cLo cHi : ℝ}
-- given
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * Real.exp (-ν * Real.log (M.betaC - β)) ≤ correlationLength β ∧ correlationLength β ≤ cHi * Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_eventually_const_mul_exact_power_le_le M correlationLength hcLo hcHi hcompare

/--
[hasCriticalNu_of_const_mul_exact_power_le_le_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_const_mul_exact_power_le_le_on_Ioo_eq
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
  {ν cLo cHi δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → cLo * Real.exp (-ν * Real.log (M.betaC - β)) ≤ correlationLength β ∧ correlationLength β ≤ cHi * Real.exp (-ν * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength ν := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_of_const_mul_exact_power_le_le_on_Ioo M correlationLength hδ hcLo hcHi hcompare

/--
[rgToExponentBridge_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_mul_log_negligible_prefactor_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : C.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  C.RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor hbridge hξpos hApos hlogA

/--
[rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : C.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  C.RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent hbridge hpred hξpos hApos hlogA

/--
[hasCriticalNu_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_mul_log_negligible_prefactor_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : C.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_mul_log_negligible_prefactor C hbridge hξpos hApos hlogA

/--
[Valid.mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma mul_log_negligible_prefactor_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hC : C.Valid correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  C.Valid (fun β => A β * correlationLength β) where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.RGCertificate.Valid.mul_log_negligible_prefactor hC hξpos hApos hlogA

/--
[Valid.hasCriticalNu_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_mul_log_negligible_prefactor_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hC : C.Valid correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.Valid.hasCriticalNu_mul_log_negligible_prefactor hC hξpos hApos hlogA

/--
[rgToExponentBridge_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_const_mul_le_le_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : C.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  C.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le hbridge hξpos hcLo hcHi hcompare

/--
[rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : C.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  C.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent hbridge hpred hξpos hcLo hcHi hcompare

/--
[hasCriticalNu_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_le_le_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : C.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_eventually_const_mul_le_le C hbridge hξpos hcLo hcHi hcompare

/--
[Valid.of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma of_eventually_const_mul_le_le_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hC : C.Valid correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  C.Valid comparisonLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.RGCertificate.Valid.of_eventually_const_mul_le_le hC hξpos hcLo hcHi hcompare

/--
[Valid.hasCriticalNu_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_le_le_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hC : C.Valid correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.Valid.hasCriticalNu_of_eventually_const_mul_le_le hC hξpos hcLo hcHi hcompare

/--
[rgToExponentBridge_of_eventually_const_mul_exact_power_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_const_mul_exact_power_le_le_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤ correlationLength β ∧ correlationLength β ≤ cHi * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_const_mul_exact_power_le_le C correlationLength hcLo hcHi hcompare

/--
[hasCriticalNu_of_eventually_const_mul_exact_power_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_exact_power_le_le_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤ correlationLength β ∧ correlationLength β ≤ cHi * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_eventually_const_mul_exact_power_le_le C correlationLength hcLo hcHi hcompare

/--
[valid_of_eventually_const_mul_exact_power_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_const_mul_exact_power_le_le_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤ correlationLength β ∧ correlationLength β ≤ cHi * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_eventually_const_mul_exact_power_le_le C correlationLength hcLo hcHi hcompare hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_const_mul_exact_power_le_le_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_const_mul_exact_power_le_le_on_Ioo_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {cLo cHi δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → cLo * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤ correlationLength β ∧ correlationLength β ≤ cHi * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_const_mul_exact_power_le_le_on_Ioo C correlationLength hδ hcLo hcHi hcompare

/--
[hasCriticalNu_of_const_mul_exact_power_le_le_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_const_mul_exact_power_le_le_on_Ioo_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {cLo cHi δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → cLo * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤ correlationLength β ∧ correlationLength β ≤ cHi * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_const_mul_exact_power_le_le_on_Ioo C correlationLength hδ hcLo hcHi hcompare

/--
[valid_of_const_mul_exact_power_le_le_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_const_mul_exact_power_le_le_on_Ioo_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {cLo cHi δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → cLo * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) ≤ correlationLength β ∧ correlationLength β ≤ cHi * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_const_mul_exact_power_le_le_on_Ioo C correlationLength hδ hcLo hcHi hcompare hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_prefactor_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_exact_power_prefactor C correlationLength hA hξ

/--
[hasCriticalNu_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_prefactor_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_eventually_exact_power_prefactor C correlationLength hA hξ

/--
[valid_of_eventually_exact_power_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_prefactor_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_eventually_exact_power_prefactor C correlationLength hA hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_exact_power_prefactor_congr_predictedExponent C D correlationLength hpred hA hξ

/--
[hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_eventually_exact_power_prefactor_congr_predictedExponent C D correlationLength hpred hA hξ

/--
[valid_of_eventually_exact_power_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_eventually_exact_power_prefactor_congr_predictedExponent C D correlationLength hpred hA hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_prefactor_on_Ioo_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_exact_power_prefactor_on_Ioo C correlationLength δ hA hδ hξ

/--
[hasCriticalNu_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_prefactor_on_Ioo_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_exact_power_prefactor_on_Ioo C correlationLength δ hA hδ hξ

/--
[valid_of_exact_power_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_prefactor_on_Ioo_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_exact_power_prefactor_on_Ioo C correlationLength δ hA hδ hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_exact_power_prefactor_on_Ioo_congr_predictedExponent C D correlationLength δ hpred hA hδ hξ

/--
[hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_exact_power_prefactor_on_Ioo_congr_predictedExponent C D correlationLength δ hpred hA hδ hξ

/--
[valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {A : ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hA : 0 < A)
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_exact_power_prefactor_on_Ioo_congr_predictedExponent C D correlationLength δ hpred hA hδ hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_variable_prefactor_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_exact_power_variable_prefactor C correlationLength A hA hlogA hξ

/--
[hasCriticalNu_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_variable_prefactor_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_eventually_exact_power_variable_prefactor C correlationLength A hA hlogA hξ

/--
[valid_of_eventually_exact_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_variable_prefactor_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_eventually_exact_power_variable_prefactor C correlationLength A hA hlogA hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_exact_power_variable_prefactor_congr_predictedExponent C D correlationLength A hpred hA hlogA hξ

/--
[hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_eventually_exact_power_variable_prefactor_congr_predictedExponent C D correlationLength A hpred hA hlogA hξ

/--
[valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hA : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_eventually_exact_power_variable_prefactor_congr_predictedExponent C D correlationLength A hpred hA hlogA hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo C correlationLength A δ hδ hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo C correlationLength A δ hδ hA hlogA hξ

/--
[valid_of_exact_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_variable_prefactor_on_Ioo_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-C.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_exact_power_variable_prefactor_on_Ioo C correlationLength A δ hδ hA hlogA hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_pred C D correlationLength A δ hpred hδ hA hlogA hξ

/--
[rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent C D correlationLength A δ hpred hδ hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_pred C D correlationLength A δ hpred hδ hA hlogA hξ

/--
[hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent C D correlationLength A δ hpred hδ hA hlogA hξ

/--
[valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_exact_power_variable_prefactor_on_Ioo_congr_pred C D correlationLength A δ hpred hδ hA hlogA hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hA : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = A β * Real.exp (-D.predictedExponent * Real.log (M.betaC - β)))
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_exact_power_variable_prefactor_on_Ioo_congr_predictedExponent C D correlationLength A δ hpred hδ hA hlogA hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo C correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo C correlationLength mass B δ hδ hB hlogB hmass hξ

/--
[valid_of_exact_mass_power_variable_prefactor_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_mass_power_variable_prefactor_on_Ioo_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹)
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_exact_mass_power_variable_prefactor_on_Ioo C correlationLength mass B δ hδ hB hlogB hmass hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred C D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent C D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred C D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent C D correlationLength mass B δ hpred hδ hB hlogB hmass hξ

/--
[valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹)
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_pred C D correlationLength mass B δ hpred hδ hB hlogB hmass hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hδ : 0 < δ)
  (hB : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = (mass β)⁻¹)
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_exact_mass_power_variable_prefactor_on_Ioo_congr_predictedExponent C D correlationLength mass B δ hpred hδ hB hlogB hmass hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor C correlationLength mass B hB hlogB hmass hξ

/--
[hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_eq_2
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor C correlationLength mass B hB hlogB hmass hξ

/--
[valid_of_eventually_exact_mass_power_variable_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_mass_power_variable_prefactor_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹)
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_eventually_exact_mass_power_variable_prefactor C correlationLength mass B hB hlogB hmass hξ hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent C D correlationLength mass B hpred hB hlogB hmass hξ

/--
[hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent C D correlationLength mass B hpred hB hlogB hmass hξ

/--
[valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PowerLawBridge.lean)
-/
@[path]
private lemma valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength mass B : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hB : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < B β)
  (hlogB : Filter.Tendsto (fun β : ℝ => Real.log (B β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
  (hmass : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), mass β = B β * Real.exp (D.predictedExponent * Real.log (M.betaC - β)))
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = (mass β)⁻¹)
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_eventually_exact_mass_power_variable_prefactor_congr_predictedExponent C D correlationLength mass B hpred hB hlogB hmass hξ hfinite htail hfixed hlinear hhyperbolic horbit


-- created on 2026-10-23
