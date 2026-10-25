import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteWitnessPackage StatMech.Exact3D.InfiniteTailWitnessPackage StatMech.Exact3D.InfiniteTailTableWitnessPackage StatMech.Exact3D.FinitePlusTailHyperbolicSplitting StatMech.Exact3D.FinitePlusTailBlockRGPackage StatMech.Exact3D.FinitePlusTailClosedBallRGPackage StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage


/--
[valid_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_mul_log_negligible_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_mul_log_negligible_prefactor W hbridge hξpos hApos hlogA

/--
[hasCriticalNu_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_mul_log_negligible_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_mul_log_negligible_prefactor W hbridge hξpos hApos hlogA

/--
[valid_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_mul_log_negligible_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_mul_log_negligible_prefactor_congr_predictedExponent W hbridge hpred hξpos hApos hlogA

/--
[hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent W hbridge hpred hξpos hApos hlogA

/--
[rgToExponentBridge_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_mul_log_negligible_prefactor_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_mul_log_negligible_prefactor W hbridge hξpos hApos hlogA

/--
[rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent W hbridge hpred hξpos hApos hlogA

/--
[rgToExponentBridge_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_const_mul_le_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_eventually_const_mul_le_le W hbridge hpos hcLo hcHi hcompare

/--
[valid_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_of_eventually_const_mul_le_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_eventually_const_mul_le_le W hbridge hpos hcLo hcHi hcompare

/--
[hasCriticalNu_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_le_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le W hbridge hpos hcLo hcHi hcompare

/--
[rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent W hbridge hpred hpos hcLo hcHi hcompare

/--
[valid_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_of_eventually_const_mul_le_le_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_eventually_const_mul_le_le_congr_predictedExponent W hbridge hpred hpos hcLo hcHi hcompare

/--
[hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent W hbridge hpred hpos hcLo hcHi hcompare

/--
[valid_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_mul_log_negligible_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_mul_log_negligible_prefactor W hbridge hξpos hApos hlogA

/--
[hasCriticalNu_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_mul_log_negligible_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_mul_log_negligible_prefactor W hbridge hξpos hApos hlogA

/--
[valid_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_mul_log_negligible_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_mul_log_negligible_prefactor_congr_predictedExponent W hbridge hpred hξpos hApos hlogA

/--
[hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent W hbridge hpred hξpos hApos hlogA

/--
[rgToExponentBridge_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_mul_log_negligible_prefactor_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_mul_log_negligible_prefactor W hbridge hξpos hApos hlogA

/--
[rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent W hbridge hpred hξpos hApos hlogA

/--
[rgToExponentBridge_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_const_mul_le_le_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_eventually_const_mul_le_le W hbridge hpos hcLo hcHi hcompare

/--
[valid_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_of_eventually_const_mul_le_le_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_eventually_const_mul_le_le W hbridge hpos hcLo hcHi hcompare

/--
[hasCriticalNu_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_le_le_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le W hbridge hpos hcLo hcHi hcompare

/--
[rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent W hbridge hpred hpos hcLo hcHi hcompare

/--
[valid_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_of_eventually_const_mul_le_le_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_eventually_const_mul_le_le_congr_predictedExponent W hbridge hpred hpos hcLo hcHi hcompare

/--
[hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent W hbridge hpred hpos hcLo hcHi hcompare

/--
[valid_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_mul_log_negligible_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_mul_log_negligible_prefactor W hbridge hξpos hApos hlogA

/--
[hasCriticalNu_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_mul_log_negligible_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_mul_log_negligible_prefactor W hbridge hξpos hApos hlogA

/--
[valid_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_mul_log_negligible_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_mul_log_negligible_prefactor_congr_predictedExponent W hbridge hpred hξpos hApos hlogA

/--
[hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent W hbridge hpred hξpos hApos hlogA

/--
[rgToExponentBridge_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_mul_log_negligible_prefactor_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_mul_log_negligible_prefactor W hbridge hξpos hApos hlogA

/--
[rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  W.certificate.RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent W hbridge hpred hξpos hApos hlogA

/--
[rgToExponentBridge_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_const_mul_le_le_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_eventually_const_mul_le_le W hbridge hpos hcLo hcHi hcompare

/--
[valid_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_of_eventually_const_mul_le_le_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_eventually_const_mul_le_le W hbridge hpos hcLo hcHi hcompare

/--
[hasCriticalNu_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_le_le_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le W hbridge hpos hcLo hcHi hcompare

/--
[rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent W hbridge hpred hpos hcLo hcHi hcompare

/--
[valid_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma valid_of_eventually_const_mul_le_le_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  W.certificate.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.valid_of_eventually_const_mul_le_le_congr_predictedExponent W hbridge hpred hpos hcLo hcHi hcompare

/--
[hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent_eq_3
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableWitnessPackage.hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent W hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_valid_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_mul_log_negligible_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (H.certificate scale M).Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_mul_log_negligible_prefactor H scale M hbridge hξpos hApos hlogA

/--
[certificate_hasCriticalNu_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_mul_log_negligible_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_mul_log_negligible_prefactor H scale M hbridge hξpos hApos hlogA

/--
[certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (H.certificate scale M).Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent H scale M hbridge hpred hξpos hApos hlogA

/--
[certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent H scale M hbridge hpred hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_mul_log_negligible_prefactor_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (H.certificate scale M).RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_mul_log_negligible_prefactor H scale M hbridge hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (H.certificate scale M).RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent H scale M hbridge hpred hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_const_mul_le_le_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (H.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_const_mul_le_le H scale M hbridge hpos hcLo hcHi hcompare

/--
[certificate_valid_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_const_mul_le_le_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (H.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_eventually_const_mul_le_le H scale M hbridge hpos hcLo hcHi hcompare

/--
[certificate_hasCriticalNu_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_const_mul_le_le_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : (H.certificate scale M).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_const_mul_le_le H scale M hbridge hpos hcLo hcHi hcompare

/--
[certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (H.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent H scale M hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (H.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent H scale M hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent_eq
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {H : FinitePlusTailHyperbolicSplitting n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (H.certificate scale M).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength (H.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailHyperbolicSplitting.certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent H scale M hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_valid_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_mul_log_negligible_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale M).Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_mul_log_negligible_prefactor P scale M hbridge hξpos hApos hlogA

/--
[certificate_hasCriticalNu_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_mul_log_negligible_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor P scale M hbridge hξpos hApos hlogA

/--
[certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale M).Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent P scale M hbridge hpred hξpos hApos hlogA

/--
[certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent P scale M hbridge hpred hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_mul_log_negligible_prefactor_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale M).RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_mul_log_negligible_prefactor P scale M hbridge hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale M).RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent P scale M hbridge hpred hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_const_mul_le_le_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_const_mul_le_le P scale M hbridge hpos hcLo hcHi hcompare

/--
[certificate_valid_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_const_mul_le_le_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_eventually_const_mul_le_le P scale M hbridge hpos hcLo hcHi hcompare

/--
[certificate_hasCriticalNu_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_const_mul_le_le_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le P scale M hbridge hpos hcLo hcHi hcompare

/--
[certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent P scale M hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent P scale M hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent_eq_2
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailBlockRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailBlockRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent P scale M hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_valid_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_mul_log_negligible_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale M).Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_mul_log_negligible_prefactor P scale M hbridge hξpos hApos hlogA

/--
[certificate_hasCriticalNu_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_mul_log_negligible_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor P scale M hbridge hξpos hApos hlogA

/--
[certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale M).Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent P scale M hbridge hpred hξpos hApos hlogA

/--
[certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent P scale M hbridge hpred hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_mul_log_negligible_prefactor_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale M).RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_mul_log_negligible_prefactor P scale M hbridge hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale M).RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent P scale M hbridge hpred hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_const_mul_le_le_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_const_mul_le_le P scale M hbridge hpos hcLo hcHi hcompare

/--
[certificate_valid_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_const_mul_le_le_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le P scale M hbridge hpos hcLo hcHi hcompare

/--
[certificate_hasCriticalNu_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_const_mul_le_le_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : (P.certificate scale M).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le P scale M hbridge hpos hcLo hcHi hcompare

/--
[certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale M).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent P scale M hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale M).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent P scale M hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent_eq_3
  {n : ℕ}
  {α : Type}
  {M : CriticalModel ι}
  {P : FinitePlusTailClosedBallRGPackage n α}
  {scale : BlockScale}
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale M).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale M).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FinitePlusTailClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent P scale M hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_valid_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_mul_log_negligible_prefactor_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale).Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_mul_log_negligible_prefactor P scale hbridge hξpos hApos hlogA

/--
[certificate_hasCriticalNu_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_mul_log_negligible_prefactor_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor P scale hbridge hξpos hApos hlogA

/--
[certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale).Valid (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_mul_log_negligible_prefactor_congr_predictedExponent P scale hbridge hpred hξpos hApos hlogA

/--
[certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  HasCriticalNu M (fun β => A β * correlationLength β) (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_mul_log_negligible_prefactor_congr_predictedExponent P scale hbridge hpred hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_mul_log_negligible_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_mul_log_negligible_prefactor_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale).RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_mul_log_negligible_prefactor P scale hbridge hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength A : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hξpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hApos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < A β)
  (hlogA : Filter.Tendsto (fun β : ℝ => Real.log (A β) / Real.log (M.betaC - β)) (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)) :
-- imply
  (P.certificate scale).RGToExponentBridge (fun β => A β * correlationLength β) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_mul_log_negligible_prefactor_congr_predictedExponent P scale hbridge hpred hξpos hApos hlogA

/--
[certificate_rgToExponentBridge_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_const_mul_le_le_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_const_mul_le_le P scale hbridge hpos hcLo hcHi hcompare

/--
[certificate_valid_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_const_mul_le_le_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le P scale hbridge hpos hcLo hcHi hcompare

/--
[certificate_hasCriticalNu_of_eventually_const_mul_le_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_const_mul_le_le_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le P scale hbridge hpos hcLo hcHi hcompare

/--
[certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale).RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_eventually_const_mul_le_le_congr_predictedExponent P scale hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  (P.certificate scale).Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_eventually_const_mul_le_le_congr_predictedExponent P scale hbridge hpred hpos hcLo hcHi hcompare

/--
[certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridge.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent_eq_4
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
  {cLo cHi : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hpos : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < correlationLength β)
  (hcLo : 0 < cLo)
  (hcHi : 0 < cHi)
  (hcompare : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), cLo * correlationLength β ≤ comparisonLength β ∧ comparisonLength β ≤ cHi * correlationLength β) :
-- imply
  HasCriticalNu M comparisonLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_eventually_const_mul_le_le_congr_predictedExponent P scale hbridge hpred hpos hcLo hcHi hcompare


-- created on 2026-10-23
