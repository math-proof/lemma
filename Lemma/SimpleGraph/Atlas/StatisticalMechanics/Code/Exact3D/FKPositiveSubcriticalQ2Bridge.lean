import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
open Filter MeasureTheory StatMech StatMech.Exact3D StatMech.Exact3D.FinsetFiberIndex


/--
[FreeQ2PositiveSubcriticalComparison.belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma belowBetaC_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison) :
-- imply
  FreeQ2PositiveSubcriticalComparisonBelowBetaC := by
-- proof
  apply StatMech.Exact3D.FreeQ2PositiveSubcriticalComparison.belowBetaC hcmp

/--
[freeQ2PositiveSubcriticalComparisonBelowBetaC_of_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2PositiveSubcriticalComparisonBelowBetaC_of_restrictedCylinderComparison_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC) :
-- imply
  FreeQ2PositiveSubcriticalComparisonBelowBetaC := by
-- proof
  apply StatMech.Exact3D.freeQ2PositiveSubcriticalComparisonBelowBetaC_of_restrictedCylinderComparison hcmp

/--
[freeIsingThermodynamicLimitPositiveSubcritical_of_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeIsingThermodynamicLimitPositiveSubcritical_of_restrictedCylinderComparison_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC) :
-- imply
  FreeIsingThermodynamicLimitPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeIsingThermodynamicLimitPositiveSubcritical_of_restrictedCylinderComparison hcmp

/--
[freeFullVolumeQ2ThermodynamicLimitPositiveSubcritical_of_freeIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeFullVolumeQ2ThermodynamicLimitPositiveSubcritical_of_freeIsing_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical) :
-- imply
  FreeFullVolumeQ2ThermodynamicLimitPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeFullVolumeQ2ThermodynamicLimitPositiveSubcritical_of_freeIsing hlim

/--
[freeQ2AdditiveComparePositiveSubcritical_of_freeIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2AdditiveComparePositiveSubcritical_of_freeIsing_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical) :
-- imply
  FreeQ2AdditiveComparePositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2AdditiveComparePositiveSubcritical_of_freeIsing hlim

/--
[PositiveSubexponentialPrefactor.const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma const_eq
  {c : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  PositiveSubexponentialPrefactor (fun _ : ℕ => c) := by
-- proof
  apply StatMech.Exact3D.PositiveSubexponentialPrefactor.const hc

/--
[PositiveSubexponentialPrefactor.add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma add_eq
  {A B : ℕ → ℝ}
-- given
  (hA : PositiveSubexponentialPrefactor A)
  (hB : PositiveSubexponentialPrefactor B) :
-- imply
  PositiveSubexponentialPrefactor (fun n => A n + B n) := by
-- proof
  apply StatMech.Exact3D.PositiveSubexponentialPrefactor.add hA hB

/--
[PositiveSubexponentialPrefactor.mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma mul_eq
  {A B : ℕ → ℝ}
-- given
  (hA : PositiveSubexponentialPrefactor A)
  (hB : PositiveSubexponentialPrefactor B) :
-- imply
  PositiveSubexponentialPrefactor (fun n => A n * B n) := by
-- proof
  apply StatMech.Exact3D.PositiveSubexponentialPrefactor.mul hA hB

/--
[PositiveSubexponentialPrefactor.const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma const_mul_eq
  {A : ℕ → ℝ}
  {c : ℝ}
-- given
  (hc : 0 < c)
  (hA : PositiveSubexponentialPrefactor A) :
-- imply
  PositiveSubexponentialPrefactor (fun n => c * A n) := by
-- proof
  apply StatMech.Exact3D.PositiveSubexponentialPrefactor.const_mul hc hA

/--
[PositiveSubexponentialPrefactor.natCast_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma natCast_pow_eq
  {k : ℕ} :
-- imply
  PositiveSubexponentialPrefactor (fun n : ℕ => (n : ℝ) ^ k) := by
-- proof
  apply StatMech.Exact3D.PositiveSubexponentialPrefactor.natCast_pow k

/--
[PositiveSubexponentialPrefactor.eventually_le_exp_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma eventually_le_exp_mul_eq
  {A : ℕ → ℝ}
  {ε : ℝ}
-- given
  (hA : PositiveSubexponentialPrefactor A)
  (hε : 0 < ε) :
-- imply
  ∀ᶠ n in atTop, A n ≤ Real.exp (ε * (n : ℝ)) := by
-- proof
  apply StatMech.Exact3D.PositiveSubexponentialPrefactor.eventually_le_exp_mul hA hε

/--
[PositiveSubexponentialPrefactor.congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma congr_eq
  {A B : ℕ → ℝ}
-- given
  (hAB : ∀ᶠ n in atTop, A n = B n)
  (hA : PositiveSubexponentialPrefactor A) :
-- imply
  PositiveSubexponentialPrefactor B := by
-- proof
  apply StatMech.Exact3D.PositiveSubexponentialPrefactor.congr hAB hA

/--
[boxBoundaryCard3_eventually_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxBoundaryCard3_eventually_eq_eq :
-- imply
  ∀ᶠ n in atTop, ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) = 24 * (n : ℝ) ^ 2 + 2 := by
-- proof
  apply StatMech.Exact3D.boxBoundaryCard3_eventually_eq

/--
[boxBoundaryCard3_eventually_le_26_mul_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxBoundaryCard3_eventually_le_26_mul_sq_eq :
-- imply
  ∀ᶠ n in atTop, ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) ≤ 26 * (n : ℝ) ^ 2 := by
-- proof
  apply StatMech.Exact3D.boxBoundaryCard3_eventually_le_26_mul_sq

/--
[boxBoundaryCard3_positiveSubexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxBoundaryCard3_positiveSubexponentialPrefactor_eq :
-- imply
  PositiveSubexponentialPrefactor (fun n : ℕ => ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)) := by
-- proof
  apply StatMech.Exact3D.boxBoundaryCard3_positiveSubexponentialPrefactor

/--
[boxBoundaryCard3_mul_positiveSubexponentialPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxBoundaryCard3_mul_positiveSubexponentialPrefactor_eq
  {A : ℕ → ℝ}
-- given
  (hA : PositiveSubexponentialPrefactor A) :
-- imply
  PositiveSubexponentialPrefactor (fun n : ℕ => ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * A n) := by
-- proof
  apply StatMech.Exact3D.boxBoundaryCard3_mul_positiveSubexponentialPrefactor hA

/--
[exists_positiveSubexponentialPrefactor_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma exists_positiveSubexponentialPrefactor_add_eq
  {A B : ℕ → ℝ}
-- given
  (hApos : ∀ᶠ n in atTop, 0 < A n)
  (hBpos : ∀ᶠ n in atTop, 0 < B n)
  (hlogA : Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ)) atTop (nhds 0))
  (hlogB : Tendsto (fun n : ℕ => Real.log (B n) / (n : ℝ)) atTop (nhds 0)) :
-- imply
  ∃ C : ℕ → ℝ, (∀ᶠ n in atTop, 0 < C n) ∧ Tendsto (fun n : ℕ => Real.log (C n) / (n : ℝ)) atTop (nhds 0) ∧ ∀ᶠ n in atTop, A n + B n ≤ C n := by
-- proof
  apply StatMech.Exact3D.exists_positiveSubexponentialPrefactor_add hApos hBpos hlogA hlogB

/--
[freeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical_trivial_eq :
-- imply
  FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical_trivial

/--
[freeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical_of_pointwiseEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical_of_pointwiseEnvelope_eq
-- given
  (hprofile : FreeQ2BoundaryProfilePointwiseEnvelopeForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical_of_pointwiseEnvelope hprofile

/--
[freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexEnvelope_eq
-- given
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexEnvelopeForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexEnvelope hprofile

/--
[freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer_shift_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβpos : 0 < β) :
-- imply
  Monotone fun k : ℕ => freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (n + k) n := by
-- proof
  apply StatMech.Exact3D.freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer_shift β hβpos n

/--
[freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer_eq
  {β : ℝ}
  {n M₁ M₂ : ℕ}
-- given
  (hβpos : 0 < β)
  (hM₁ : n ≤ M₁)
  (hM : M₁ ≤ M₂) :
-- imply
  freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M₁ n ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M₂ n := by
-- proof
  apply StatMech.Exact3D.freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer β hβpos hM₁ hM

/--
[freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profilePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profilePolynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profilePolynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileFiniteVolumeComparisonToXAxis_of_profileFiniteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteVolumeComparisonToXAxis_of_profileFiniteVolumePolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileFiniteVolumeComparisonToXAxis_of_profileFiniteVolumePolynomial hcompare

/--
[freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_finiteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_finiteVolumePolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_finiteVolumePolynomial hcompare

/--
[freeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxis_of_scaledFiniteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxis_of_scaledFiniteVolumePolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxis_of_scaledFiniteVolumePolynomial hcompare

/--
[freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumeComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumeComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileFiniteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileFiniteVolumePolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileFiniteVolumePolynomial hcompare

/--
[freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileScaledFiniteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileScaledFiniteVolumePolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileScaledFiniteVolumePolynomial hcompare

/--
[freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumePolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumePolynomial hcompare

/--
[freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileScaledFiniteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileScaledFiniteVolumePolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileScaledFiniteVolumePolynomial hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_profilePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_profilePolynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpSameMass_of_profilePolynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_profileFiniteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_profileFiniteVolumeComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpSameMass_of_profileFiniteVolumeComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_profileFiniteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_profileFiniteVolumePolynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpSameMass_of_profileFiniteVolumePolynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_profileScaledFiniteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_profileScaledFiniteVolumePolynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSubexpSameMass_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryVertexSubexpComparisonToXAxis_of_polynomialComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexSubexpComparisonToXAxis_of_polynomialComparison_eq
-- given
  (hcompare : FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryVertexSubexpComparisonToXAxis_of_polynomialComparison hcompare

/--
[freeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at_eq
-- given
  (hcompare : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisAt β hβpos n) :
-- imply
  FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at hcompare

/--
[freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at_eq
-- given
  (hcompare : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at hcompare

/--
[freeQ2BoundaryProfileDoubleScaleAt_of_vertexDoubleScaleAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScaleAt_of_vertexDoubleScaleAt_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβpos : 0 < β)
  (hpoint : FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisAt β hβpos n) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileDoubleScaleAt_of_vertexDoubleScaleAt β hβpos n hpoint

/--
[freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_vertex_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_vertex_at_eq
-- given
  (hpoint : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisAt β hβpos n) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_vertex_at hpoint

/--
[freeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical_of_eventually_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical_of_eventually_at_eq
-- given
  (hfinite : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt β hβpos n) :
-- imply
  FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical_of_eventually_at hfinite

/--
[finiteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical_of_eventually_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical_of_eventually_at_eq
-- given
  (hSimon : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FiniteQ2SimonFreeBoundaryIsingBoxAt β n) :
-- imply
  FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical_of_eventually_at hSimon

/--
[finiteQ2SimonFreeBoundaryExpectationJPositiveSubcritical_of_eventually_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonFreeBoundaryExpectationJPositiveSubcritical_of_eventually_at_eq
-- given
  (hSimon : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FiniteQ2SimonFreeBoundaryExpectationJAt β n) :
-- imply
  FiniteQ2SimonFreeBoundaryExpectationJPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2SimonFreeBoundaryExpectationJPositiveSubcritical_of_eventually_at hSimon

/--
[finiteCurrentTwoPointRatio_eq_expectationJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteCurrentTwoPointRatio_eq_expectationJ_eq
  {d n : ℕ}
  {β : ℝ}
  {x y : FK.boxVerts d n} :
-- imply
  finiteCurrentTwoPointRatio d n β x y = Sharpness.expectationJ (FK.boxGraph d n) β (fun _ => 1) (finiteTwoPointSource d n x y) := by
-- proof
  apply StatMech.Exact3D.finiteCurrentTwoPointRatio_eq_expectationJ d n β x y

/--
[expectationJ_empty_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma expectationJ_empty_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  Sharpness.expectationJ G β J (∅ : Finset V) = 1 := by
-- proof
  apply StatMech.Exact3D.expectationJ_empty_eq_one G β J

/--
[currentSum_empty_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma currentSum_empty_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  0 < Sharpness.currentSum G β J (∅ : Finset V) := by
-- proof
  apply StatMech.Exact3D.currentSum_empty_pos G β J

/--
[currentSum_empty_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma currentSum_empty_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  Sharpness.currentSum G β J (∅ : Finset V) ≠ 0 := by
-- proof
  apply StatMech.Exact3D.currentSum_empty_ne_zero G β J

/--
[currentSum_pos_of_positive_edgeCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma currentSum_pos_of_positive_edgeCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {m : ↥G.edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hsrc : Sharpness.sources G (Sharpness.ofEdgeFun G m) = A)
  (hweight : 0 < Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) :
-- imply
  0 < Sharpness.currentSum G β J A := by
-- proof
  apply StatMech.Exact3D.currentSum_pos_of_positive_edgeCurrent G β J A hβ hJ m hsrc hweight

/--
[expectationJ_pos_of_positive_edgeCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma expectationJ_pos_of_positive_edgeCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {m : ↥G.edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hsrc : Sharpness.sources G (Sharpness.ofEdgeFun G m) = A)
  (hweight : 0 < Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) :
-- imply
  0 < Sharpness.expectationJ G β J A := by
-- proof
  apply StatMech.Exact3D.expectationJ_pos_of_positive_edgeCurrent G β J A hβ hJ m hsrc hweight

/--
[currentSum_pos_of_expectationJ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma currentSum_pos_of_expectationJ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hpos : 0 < Sharpness.expectationJ G β J A) :
-- imply
  0 < Sharpness.currentSum G β J A := by
-- proof
  apply StatMech.Exact3D.currentSum_pos_of_expectationJ_pos G β J A hpos

/--
[sourcePairSum_empty_pos_of_expectationJ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sourcePairSum_empty_pos_of_expectationJ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hpos : 0 < Sharpness.expectationJ G β J A) :
-- imply
  0 < Sharpness.sourcePairSum G β J A (∅ : Finset V) := by
-- proof
  apply StatMech.Exact3D.sourcePairSum_empty_pos_of_expectationJ_pos G β J A hpos

/--
[sourcePairSum_pos_of_expectationJ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sourcePairSum_pos_of_expectationJ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
-- given
  (hA : 0 < Sharpness.expectationJ G β J A)
  (hB : 0 < Sharpness.expectationJ G β J B) :
-- imply
  0 < Sharpness.sourcePairSum G β J A B := by
-- proof
  apply StatMech.Exact3D.sourcePairSum_pos_of_expectationJ_pos G β J A B hA hB

/--
[currentSum_ratio_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma currentSum_ratio_le_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {r : ℝ} :
-- imply
  Sharpness.currentSum G β J A / Sharpness.currentSum G β J (∅ : Finset V) ≤ r ↔ Sharpness.currentSum G β J A ≤ r * Sharpness.currentSum G β J (∅ : Finset V) := by
-- proof
  apply StatMech.Exact3D.currentSum_ratio_le_iff G β J A r

/--
[currentSum_eq_zero_of_expectationJ_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma currentSum_eq_zero_of_expectationJ_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hzero : Sharpness.expectationJ G β J A = 0) :
-- imply
  Sharpness.currentSum G β J A = 0 := by
-- proof
  apply StatMech.Exact3D.currentSum_eq_zero_of_expectationJ_eq_zero G β J A hzero

/--
[sourcePairSum_empty_eq_zero_of_expectationJ_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sourcePairSum_empty_eq_zero_of_expectationJ_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hzero : Sharpness.expectationJ G β J A = 0) :
-- imply
  Sharpness.sourcePairSum G β J A (∅ : Finset V) = 0 := by
-- proof
  apply StatMech.Exact3D.sourcePairSum_empty_eq_zero_of_expectationJ_eq_zero G β J A hzero

/--
[currentSum_bound_of_sourcePairSum_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma currentSum_bound_of_sourcePairSum_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {r : ℝ}
-- given
  (hpair : Sharpness.sourcePairSum G β J A (∅ : Finset V) ≤ r * Sharpness.sourcePairSum G β J (∅ : Finset V) (∅ : Finset V)) :
-- imply
  Sharpness.currentSum G β J A ≤ r * Sharpness.currentSum G β J (∅ : Finset V) := by
-- proof
  apply StatMech.Exact3D.currentSum_bound_of_sourcePairSum_bound G β J A r hpair

/--
[expectationJ_le_of_sourcePairSum_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma expectationJ_le_of_sourcePairSum_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {r : ℝ}
-- given
  (hpair : Sharpness.sourcePairSum G β J A (∅ : Finset V) ≤ r * Sharpness.sourcePairSum G β J (∅ : Finset V) (∅ : Finset V)) :
-- imply
  Sharpness.expectationJ G β J A ≤ r := by
-- proof
  apply StatMech.Exact3D.expectationJ_le_of_sourcePairSum_bound G β J A r hpair

/--
[edgeCopySourcePairSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSummand_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {m : ↥G.edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ edgeCopySourcePairSummand G β J A B m := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSummand_nonneg G β J A B m hβ hJ

/--
[weight_ofEdgeFun_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma weight_ofEdgeFun_mono_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β γ : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hβγ : β ≤ γ)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  Sharpness.weight G β J (Sharpness.ofEdgeFun G m) ≤ Sharpness.weight G γ J (Sharpness.ofEdgeFun G m) := by
-- proof
  apply StatMech.Exact3D.weight_ofEdgeFun_mono_beta G hβ hβγ J hJ m

/--
[edgeCopySourcePairSplitCount_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSplitCount_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {A B : Finset V} :
-- imply
  0 ≤ ∑ S : Finset (Sharpness.FluxEdgeCopy.Copy G m), (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) S = A then (1 : ℝ) else 0) * (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSplitCount_nonneg G m A B

/--
[edgeCopySourcePairSummand_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSummand_mono_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β γ : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {m : ↥G.edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hβγ : β ≤ γ)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  edgeCopySourcePairSummand G β J A B m ≤ edgeCopySourcePairSummand G γ J A B m := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSummand_mono_beta G hβ hβγ J hJ A B m

/--
[edgeCopySourcePairDataWeight_le_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairDataWeight_le_summand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {d : edgeCopySourcePairData G A B}
-- given
  (hweight : 0 ≤ edgeCopySourcePairDataWeight G β J d) :
-- imply
  edgeCopySourcePairDataWeight G β J d ≤ edgeCopySourcePairSummand G β J A B d.1 := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairDataWeight_le_summand G β J d hweight

/--
[edgeCopySourcePairSummand_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSummand_summable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V} :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => edgeCopySourcePairSummand G β J A B m) := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSummand_summable G β J A B

/--
[edgeCopySourcePairSummand_le_edgeCopySourcePairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSummand_le_edgeCopySourcePairSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {m : ↥G.edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  edgeCopySourcePairSummand G β J A B m ≤ edgeCopySourcePairSum G β J A B := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSummand_le_edgeCopySourcePairSum G β J A B m hβ hJ

/--
[edgeCopySourcePairSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ edgeCopySourcePairSum G β J A B := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSum_nonneg G β J A B hβ hJ

/--
[edgeCopySourcePairSum_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSum_mono_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β γ : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hβγ : β ≤ γ)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  edgeCopySourcePairSum G β J A B ≤ edgeCopySourcePairSum G γ J A B := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSum_mono_beta G hβ hβγ J hJ A B

/--
[sourcePairSum_eq_edgeCopySourcePairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sourcePairSum_eq_edgeCopySourcePairSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V} :
-- imply
  Sharpness.sourcePairSum G β J A B = edgeCopySourcePairSum G β J A B := by
-- proof
  apply StatMech.Exact3D.sourcePairSum_eq_edgeCopySourcePairSum G β J A B

/--
[sourcePairSum_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sourcePairSum_mono_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β γ : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hβγ : β ≤ γ)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  Sharpness.sourcePairSum G β J A B ≤ Sharpness.sourcePairSum G γ J A B := by
-- proof
  apply StatMech.Exact3D.sourcePairSum_mono_beta G hβ hβγ J hJ A B

/--
[edgeCopySourcePairSum_eq_currentSum_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSum_eq_currentSum_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V} :
-- imply
  edgeCopySourcePairSum G β J A B = Sharpness.currentSum G β J A * Sharpness.currentSum G β J B := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSum_eq_currentSum_mul G β J A B

/--
[edgeCopySourcePairSum_empty_eq_collapsed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSum_empty_eq_collapsed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  edgeCopySourcePairSum G β J A (∅ : Finset V) = edgeCopySourcePairEmptyCollapsedSum G β J A := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSum_empty_eq_collapsed G β J A

/--
[edgeCopySourcePairEmptyCollapsedSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairEmptyCollapsedSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ edgeCopySourcePairEmptyCollapsedSum G β J A := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairEmptyCollapsedSum_nonneg G β J A hβ hJ

/--
[edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  edgeCopySourcePairEmptyCollapsedSum G β J A = Sharpness.currentSum G β J A * Sharpness.currentSum G β J (∅ : Finset V) := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul G β J A

/--
[edgeCopySourcePairEmptyCollapsedSum_empty_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairEmptyCollapsedSum_empty_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ} :
-- imply
  0 < edgeCopySourcePairEmptyCollapsedSum G β J (∅ : Finset V) := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairEmptyCollapsedSum_empty_pos G β J

/--
[edgeCopySourcePairEmptyCollapsedSummand_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairEmptyCollapsedSummand_summable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V} :
-- imply
  Summable (fun m : ↥G.edgeFinset → ℕ => ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A then (1 : ℝ) else 0) * (((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).powerset.filter (fun K => Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) K = A)).card : ℝ)) * Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairEmptyCollapsedSummand_summable G β J A

/--
[sourcePairBound_of_edgeCopyBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sourcePairBound_of_edgeCopyBound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {r : ℝ}
-- given
  (h : edgeCopySourcePairSum G β J A (∅ : Finset V) ≤ r * edgeCopySourcePairSum G β J (∅ : Finset V) (∅ : Finset V)) :
-- imply
  Sharpness.sourcePairSum G β J A (∅ : Finset V) ≤ r * Sharpness.sourcePairSum G β J (∅ : Finset V) (∅ : Finset V) := by
-- proof
  apply StatMech.Exact3D.sourcePairBound_of_edgeCopyBound G β J A r h

/--
[edgeCopyBound_of_emptyCollapsedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopyBound_of_emptyCollapsedBound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {r : ℝ}
-- given
  (h : edgeCopySourcePairEmptyCollapsedSum G β J A ≤ r * edgeCopySourcePairEmptyCollapsedSum G β J (∅ : Finset V)) :
-- imply
  edgeCopySourcePairSum G β J A (∅ : Finset V) ≤ r * edgeCopySourcePairSum G β J (∅ : Finset V) (∅ : Finset V) := by
-- proof
  apply StatMech.Exact3D.edgeCopyBound_of_emptyCollapsedBound G β J A r h

/--
[edgeCopySourcePairSum_empty_eq_zero_of_expectationJ_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopySourcePairSum_empty_eq_zero_of_expectationJ_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hzero : Sharpness.expectationJ G β J A = 0) :
-- imply
  edgeCopySourcePairSum G β J A (∅ : Finset V) = 0 := by
-- proof
  apply StatMech.Exact3D.edgeCopySourcePairSum_empty_eq_zero_of_expectationJ_eq_zero G β J A hzero

/--
[weight_ofEdgeFun_eq_zero_of_edge_coupling_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma weight_ofEdgeFun_eq_zero_of_edge_coupling_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {e : ↥G.edgeFinset}
-- given
  (hm : 0 < m e)
  (hJ : J e.1 = 0) :
-- imply
  Sharpness.weight G β J (Sharpness.ofEdgeFun G m) = 0 := by
-- proof
  apply StatMech.Exact3D.weight_ofEdgeFun_eq_zero_of_edge_coupling_eq_zero G β J m e hm hJ

/--
[weight_ofEdgeFun_nonneg_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma weight_ofEdgeFun_nonneg_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
-- proof
  apply StatMech.Exact3D.weight_ofEdgeFun_nonneg_of_nonneg G β J hβ hJ m

/--
[weight_ofEdgeFun_pos_of_pos_on_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma weight_ofEdgeFun_pos_of_pos_on_support_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
-- given
  (hβ : 0 < β)
  (hJ : ∀ e : ↥G.edgeFinset, 0 < m e → 0 < J e.1) :
-- imply
  0 < Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
-- proof
  apply StatMech.Exact3D.weight_ofEdgeFun_pos_of_pos_on_support G β J hβ m hJ

/--
[weight_ofEdgeFun_decrement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma weight_ofEdgeFun_decrement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {e : ↥G.edgeFinset}
-- given
  (hm : 0 < m e) :
-- imply
  ((m e : ℝ) * Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) = (β * J e.1) * Sharpness.weight G β J (Sharpness.ofEdgeFun G (Function.update m e (m e - 1))) := by
-- proof
  apply StatMech.Exact3D.weight_ofEdgeFun_decrement G β J m e hm

/--
[randomCurrent_connK_firstExit_adjStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma randomCurrent_connK_firstExit_adjStep_eq
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {S : Finset V}
  {o z : V}
-- given
  (hconn : Sharpness.RandomCurrent.connK ends K o z)
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  ∃ x y : V, x ∈ S ∧ y ∉ S ∧ Sharpness.RandomCurrent.adjStep ends K x y ∧ Sharpness.RandomCurrent.connK ends K o x := by
-- proof
  apply StatMech.Exact3D.randomCurrent_connK_firstExit_adjStep ends K S hconn ho hz

/--
[randomCurrent_sources_singleton_of_ends_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma randomCurrent_sources_singleton_of_ends_eq_eq
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {ends : ι → Sym2 V}
  {i : ι}
  {a b : V}
-- given
  (hi : ends i = s(a, b)) :
-- imply
  Sharpness.RandomCurrent.sources ends ({i} : Finset ι) = {a, b} := by
-- proof
  apply StatMech.Exact3D.randomCurrent_sources_singleton_of_ends_eq ends hi

/--
[randomCurrent_sources_sdiff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma randomCurrent_sources_sdiff_singleton_eq
  [DecidableEq ι]
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {i : ι}
-- given
  (hiK : i ∈ K) :
-- imply
  Sharpness.RandomCurrent.sources ends (K \ {i}) = Sharpness.RandomCurrent.sources ends K ∆ Sharpness.RandomCurrent.sources ends ({i} : Finset ι) := by
-- proof
  apply StatMech.Exact3D.randomCurrent_sources_sdiff_singleton ends hiK

/--
[expectationJ_symmDiff_self_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma expectationJ_symmDiff_self_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x : V} :
-- imply
  Sharpness.expectationJ G β J (({x} : Finset V) ∆ {x}) = 1 := by
-- proof
  apply StatMech.Exact3D.expectationJ_symmDiff_self_eq_one G β J x

/--
[sources_ofEdgeFun_path_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sources_ofEdgeFun_path_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : V}
  {p : G.Path a b}
-- given
  (hab : a ≠ b) :
-- imply
  let m : ↥G.edgeFinset → ℕ := fun e => p.1.edges.count e.1 Sharpness.sources G (Sharpness.ofEdgeFun G m) = ({a, b} : Finset V) := by
-- proof
  apply StatMech.Exact3D.sources_ofEdgeFun_path_count G p hab

/--
[finiteCurrentTwoPointRatio_self_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteCurrentTwoPointRatio_self_eq_one_eq
  {d n : ℕ}
  {β : ℝ}
  {x : FK.boxVerts d n} :
-- imply
  finiteCurrentTwoPointRatio d n β x x = 1 := by
-- proof
  apply StatMech.Exact3D.finiteCurrentTwoPointRatio_self_eq_one d n β x

/--
[simonLieb_singletonTarget_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma simonLieb_singletonTarget_bound_eq
  {τ : V → V → ℝ}
  {o z : V}
  {S : Finset V}
  {w : V → V → ℝ}
-- given
  (hSL : Sharpness.SimonLieb τ o S w ({z} : Finset V))
  (hz : z ∉ S)
  (hzz : τ z z ≤ 1) :
-- imply
  τ o z ≤ ∑ x ∈ S, w x z := by
-- proof
  apply StatMech.Exact3D.simonLieb_singletonTarget_bound hSL hz hzz

/--
[simonLieb_singletonTarget_bound_expectationJ_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma simonLieb_singletonTarget_bound_expectationJ_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o z : V}
  {S : Finset V}
  {w : V → V → ℝ}
-- given
  (hSL : Sharpness.SimonLieb (fun a b => Sharpness.expectationJ G β J (({a} : Finset V) ∆ {b})) o S w ({z} : Finset V))
  (hz : z ∉ S) :
-- imply
  Sharpness.expectationJ G β J (({o} : Finset V) ∆ {z}) ≤ ∑ x ∈ S, w x z := by
-- proof
  apply StatMech.Exact3D.simonLieb_singletonTarget_bound_expectationJ_symmDiff G β J hSL hz

/--
[finiteCurrentTwoPointRatio_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteCurrentTwoPointRatio_nonneg_eq
  {d n : ℕ}
  {β : ℝ}
  {x y : FK.boxVerts d n}
-- given
  (hβ : 0 ≤ β) :
-- imply
  0 ≤ finiteCurrentTwoPointRatio d n β x y := by
-- proof
  apply StatMech.Exact3D.finiteCurrentTwoPointRatio_nonneg d n hβ x y

/--
[finiteCurrentBoundaryTwoPointSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteCurrentBoundaryTwoPointSum_nonneg_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β) :
-- imply
  0 ≤ finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.Exact3D.finiteCurrentBoundaryTwoPointSum_nonneg hβ n

/--
[finiteCurrentBoundaryTwoPointSum_eq_expectationJBoundarySum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteCurrentBoundaryTwoPointSum_eq_expectationJBoundarySum_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  finiteCurrentBoundaryTwoPointSum β n = ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1) (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
-- proof
  apply StatMech.Exact3D.finiteCurrentBoundaryTwoPointSum_eq_expectationJBoundarySum β n

/--
[boundaryGhostCoupling_some_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_some_some_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (bdry : V → Prop) :
-- imply
  boundaryGhostCoupling bdry H J s(some x, some y) = J s(x, y) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_some_some bdry H J x y

/--
[boundaryGhostCoupling_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_some_none_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H : ℝ}
  {J : Sym2 V → ℝ}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  boundaryGhostCoupling bdry H J s(some x, none) = if bdry x then H else 0 := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_some_none bdry H J x

/--
[boundaryGhostCoupling_none_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_none_some_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H : ℝ}
  {J : Sym2 V → ℝ}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  boundaryGhostCoupling bdry H J s(none, some x) = if bdry x then H else 0 := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_none_some bdry H J x

/--
[boundaryGhostCoupling_none_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_none_none_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H : ℝ}
  {J : Sym2 V → ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  boundaryGhostCoupling bdry H J s(none, none) = 0 := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_none_none bdry H J

/--
[boundaryGhostCoupling_some_none_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_some_none_of_boundary_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H : ℝ}
  {J : Sym2 V → ℝ}
  {x : V}
-- given
  (bdry : V → Prop)
  (hx : bdry x) :
-- imply
  boundaryGhostCoupling bdry H J s(some x, none) = H := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_some_none_of_boundary bdry J hx

/--
[boundaryGhostCoupling_some_none_of_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_some_none_of_not_boundary_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H : ℝ}
  {J : Sym2 V → ℝ}
  {x : V}
-- given
  (bdry : V → Prop)
  (hx : ¬ bdry x) :
-- imply
  boundaryGhostCoupling bdry H J s(some x, none) = 0 := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_some_none_of_not_boundary bdry J hx

/--
[boundaryGhostCoupling_none_some_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_none_some_of_boundary_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H : ℝ}
  {J : Sym2 V → ℝ}
  {x : V}
-- given
  (bdry : V → Prop)
  (hx : bdry x) :
-- imply
  boundaryGhostCoupling bdry H J s(none, some x) = H := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_none_some_of_boundary bdry J hx

/--
[boundaryGhostCoupling_none_some_of_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_none_some_of_not_boundary_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H : ℝ}
  {J : Sym2 V → ℝ}
  {x : V}
-- given
  (bdry : V → Prop)
  (hx : ¬ bdry x) :
-- imply
  boundaryGhostCoupling bdry H J s(none, some x) = 0 := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_none_some_of_not_boundary bdry J hx

/--
[boundaryGhostCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_nonneg_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H : ℝ}
  {J : Sym2 V → ℝ}
-- given
  (bdry : V → Prop)
  (hH : 0 ≤ H)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  ∀ e, 0 ≤ boundaryGhostCoupling bdry H J e := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_nonneg bdry hH hJ

/--
[boundaryGhostCoupling_zero_eq_ghostCoupling_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_zero_eq_ghostCoupling_zero_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {β : ℝ}
-- given
  (bdry : V → Prop) :
-- imply
  boundaryGhostCoupling bdry (0 : ℝ) (fun _ : Sym2 V => (1 : ℝ)) = Sharpness.FieldGhostDict.ghostCoupling (0 : ℝ) β (fun _ => 1) := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_zero_eq_ghostCoupling_zero bdry β

/--
[boundaryGhostCoupling_mono_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boundaryGhostCoupling_mono_H_eq
  [DecidableEq V]
  [DecidablePred bdry]
  {H₁ H₂ : ℝ}
  {J : Sym2 V → ℝ}
-- given
  (bdry : V → Prop)
  (hH : H₁ ≤ H₂) :
-- imply
  ∀ e, boundaryGhostCoupling bdry H₁ J e ≤ boundaryGhostCoupling bdry H₂ J e := by
-- proof
  apply StatMech.Exact3D.boundaryGhostCoupling_mono_H bdry hH J

/--
[none_not_mem_finiteBoundaryGhostOriginalSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma none_not_mem_finiteBoundaryGhostOriginalSet_eq
  {d n : ℕ} :
-- imply
  none ∉ finiteBoundaryGhostOriginalSet d n := by
-- proof
  apply StatMech.Exact3D.none_not_mem_finiteBoundaryGhostOriginalSet d n

/--
[some_mem_finiteBoundaryGhostOriginalSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma some_mem_finiteBoundaryGhostOriginalSet_eq
  {d n : ℕ}
  {x : FK.boxVerts d n} :
-- imply
  some x ∈ finiteBoundaryGhostOriginalSet d n := by
-- proof
  apply StatMech.Exact3D.some_mem_finiteBoundaryGhostOriginalSet d n x

/--
[finiteBoundaryGhostOnePointSource_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostOnePointSource_card_eq
  {d n : ℕ} :
-- imply
  (finiteBoundaryGhostOnePointSource d n).card = 2 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostOnePointSource_card d n

/--
[finiteBoundaryGhostOnePointSource_eq_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostOnePointSource_eq_symmDiff_eq
  {d n : ℕ} :
-- imply
  finiteBoundaryGhostOnePointSource d n = (({some (IsingFK.boxOrigin d n)} : Finset (Option (FK.boxVerts d n))) ∆ {none}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostOnePointSource_eq_symmDiff d n

/--
[finiteBoundaryGhost_sourceSector_connK_origin_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sourceSector_connK_origin_none_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  Sharpness.RandomCurrent.connK (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K (some (IsingFK.boxOrigin 3 n)) none := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sourceSector_connK_origin_none m K hsrc

/--
[finiteBoundaryGhost_sourceSector_has_ghostCrossingCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sourceSector_has_ghostCrossingCopy_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  ∃ v : FK.boxVerts 3 n, (∃ i ∈ K, some v ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧ none ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i) ∧ Sharpness.RandomCurrent.connK (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K (some (IsingFK.boxOrigin 3 n)) (some v) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sourceSector_has_ghostCrossingCopy m K hsrc

/--
[finiteBoundaryGhost_sourceSector_has_boundaryGhostCrossingCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sourceSector_has_boundaryGhostCrossingCopy_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = finiteBoundaryGhostOnePointSource 3 n)
  (hweight : Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
-- imply
  ∃ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v ∧ (∃ i ∈ K, some v ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧ none ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i) ∧ Sharpness.RandomCurrent.connK (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K (some (IsingFK.boxOrigin 3 n)) (some v) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sourceSector_has_boundaryGhostCrossingCopy m K hsrc hweight

/--
[finiteBoundaryGhostSourceSector_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSourceSector_mem_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)} :
-- imply
  K ∈ finiteBoundaryGhostSourceSector m ↔ Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = finiteBoundaryGhostOnePointSource 3 n := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostSourceSector_mem m K

/--
[finiteBoundaryGhostTwoPointSourceSector_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTwoPointSourceSector_mem_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)} :
-- imply
  K ∈ finiteBoundaryGhostTwoPointSourceSector m v ↔ Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostTwoPointSourceSector_mem m v K

/--
[finiteBoundaryGhostTwoPointSourceData_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTwoPointSourceData_source_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v} :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) d.1) d.2.1 = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostTwoPointSourceData_source d

/--
[finiteBoundaryGhostTwoPointSourceDataWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTwoPointSourceDataWeight_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostTwoPointSourceDataWeight_nonneg hβ hH d

/--
[finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData_source_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {S : Finset (Option (FK.boxVerts 3 n))}
  {d : finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData n v S} :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) d.1) d.2.1 = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData_source d

/--
[finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData_fullSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData_fullSource_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {S : Finset (Option (FK.boxVerts 3 n))}
  {d : finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData n v S} :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) d.1) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.1)) = S := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData_fullSource d

/--
[finiteBoundaryGhostFullSourceClassifiedTwoPointSourceDataWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostFullSourceClassifiedTwoPointSourceDataWeight_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {S : Finset (Option (FK.boxVerts 3 n))}
  {d : finiteBoundaryGhostFullSourceClassifiedTwoPointSourceData n v S}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostFullSourceClassifiedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostFullSourceClassifiedTwoPointSourceDataWeight_nonneg hβ hH d

/--
[finiteBoundaryGhostCollapsedTwoPointSourceData_fullSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedTwoPointSourceData_fullSource_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostCollapsedTwoPointSourceData n v} :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) d.1) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.1)) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedTwoPointSourceData_fullSource d

/--
[finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostCollapsedTwoPointSourceData n v}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_nonneg hβ hH d

/--
[finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :
-- imply
  Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach (fun K => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩) = ((finiteBoundaryGhostTwoPointSourceSector m v).card : ℝ) * ((β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight m v hsrc

/--
[finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight_eq_edgeCopySummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight_eq_edgeCopySummand_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :
-- imply
  Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach (fun K => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩) = (β * H) * (((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then (1 : ℝ) else 0) * (((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)).powerset.filter (fun K => Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))).card : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedTwoPointSourceSector_attach_sum_dataWeight_eq_edgeCopySummand m v hsrc

/--
[finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_mul_emptyCollapsedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_mul_emptyCollapsedSum_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ, if hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach (fun K => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩) else 0) = (β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_mul_emptyCollapsedSum v

/--
[finiteBoundaryGhostCollapsedDataWeight_fiberSummable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedDataWeight_fiberSummable_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  Summable (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => if hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach (fun K => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩) else 0) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedDataWeight_fiberSummable v

/--
[finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_indicator_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (∑' K : {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) // K ∈ finiteBoundaryGhostTwoPointSourceSector m v ∧ Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})}, finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, K⟩) = if hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach (fun K => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩) else 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedDataWeight_fiberTsum_eq_indicator m v

/--
[finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_summable_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  Summable (fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedTwoPointSourceDataWeight_summable hβ hH v

/--
[finiteBoundaryGhostCollapsedDataWeight_tsum_eq_fiberTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedDataWeight_tsum_eq_fiberTsum_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v, finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) = ∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ, if hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then Finset.sum (finiteBoundaryGhostTwoPointSourceSector m v).attach (fun K => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ⟨m, ⟨K.1, ⟨K.2, hsrc⟩⟩⟩) else 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedDataWeight_tsum_eq_fiberTsum hβ hH v

/--
[finiteBoundaryGhostCollapsedDataWeight_tsum_eq_mul_emptyCollapsedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedDataWeight_tsum_eq_mul_emptyCollapsedSum_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v, finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) = (β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedDataWeight_tsum_eq_mul_emptyCollapsedSum hβ hH v

/--
[finiteBoundaryGhostBoundaryCrossingPairs_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_mem_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
-- imply
  p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v ↔ p.1 ∈ finiteBoundaryGhostSourceSector m ∧ p.2 ∈ p.1 ∧ some v ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 ∧ none ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_mem m v p

/--
[finiteBoundaryGhostBoundaryCrossingPairs_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_card_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairs m v).card = finiteBoundaryGhostBoundaryCrossingPairCount m v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_card m v

/--
[finiteBoundaryGhostBoundaryCrossingPairCountSummand_eq_sum_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairCountSummand_eq_sum_pairs_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) = ∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairCountSummand_eq_sum_pairs m v

/--
[finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount_nat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount_nat_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (finiteBoundaryGhostBoundaryCrossingSourceSector m v).card ≤ finiteBoundaryGhostBoundaryCrossingPairCount m v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount_nat m v

/--
[finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ) ≤ (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingSourceSector_card_le_crossingPairCount m v

/--
[edgeCopy_filter_card_le_multiplicity_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma edgeCopy_filter_card_le_multiplicity_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)}
  [DecidablePred P]
-- given
  (P : ↥G.edgeFinset → Prop) :
-- imply
  (K.filter (fun i => P i.1)).card ≤ ∑ e : ↥G.edgeFinset, if P e then m e else 0 := by
-- proof
  apply StatMech.Exact3D.edgeCopy_filter_card_le_multiplicity_sum G m K P

/--
[copyDeleteEmbeddingDecrement_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeleteEmbeddingDecrement_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
  {a : Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1))} :
-- imply
  ((copyDeleteEmbeddingDecrement G m i a).1).1 = a.1 := by
-- proof
  apply StatMech.Exact3D.copyDeleteEmbeddingDecrement_fst G m i a

/--
[copyDeleteEmbeddingDecrement_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeleteEmbeddingDecrement_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
  {a : Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1))} :
-- imply
  Sharpness.FluxEdgeCopy.endsM G m ((copyDeleteEmbeddingDecrement G m i a).1) = Sharpness.FluxEdgeCopy.endsM G (Function.update m i.1 (m i.1 - 1)) a := by
-- proof
  apply StatMech.Exact3D.copyDeleteEmbeddingDecrement_ends G m i a

/--
[copyDeleteEmbeddingDecrement_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeleteEmbeddingDecrement_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m} :
-- imply
  Function.Injective (fun a : Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1)) => (copyDeleteEmbeddingDecrement G m i a).1) := by
-- proof
  apply StatMech.Exact3D.copyDeleteEmbeddingDecrement_injective G m i

/--
[copyDeleteEmbeddingDecrementEmbedding_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeleteEmbeddingDecrementEmbedding_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
  {a : Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1))} :
-- imply
  Sharpness.FluxEdgeCopy.endsM G m (copyDeleteEmbeddingDecrementEmbedding G m i a) = Sharpness.FluxEdgeCopy.endsM G (Function.update m i.1 (m i.1 - 1)) a := by
-- proof
  apply StatMech.Exact3D.copyDeleteEmbeddingDecrementEmbedding_ends G m i a

/--
[copyDeleteEmbeddingDecrementFinset_not_mem_deleted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeleteEmbeddingDecrementFinset_not_mem_deleted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1)))} :
-- imply
  i ∉ copyDeleteEmbeddingDecrementFinset G m i K := by
-- proof
  apply StatMech.Exact3D.copyDeleteEmbeddingDecrementFinset_not_mem_deleted G m i K

/--
[copyDeleteEmbeddingDecrement_degK_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeleteEmbeddingDecrement_degK_map_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1)))}
  {x : V} :
-- imply
  Sharpness.RandomCurrent.degK (Sharpness.FluxEdgeCopy.endsM G m) (copyDeleteEmbeddingDecrementFinset G m i K) x = Sharpness.RandomCurrent.degK (Sharpness.FluxEdgeCopy.endsM G (Function.update m i.1 (m i.1 - 1))) K x := by
-- proof
  apply StatMech.Exact3D.copyDeleteEmbeddingDecrement_degK_map G m i K x

/--
[copyDeleteEmbeddingDecrement_sources_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeleteEmbeddingDecrement_sources_map_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1)))} :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) (copyDeleteEmbeddingDecrementFinset G m i K) = Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G (Function.update m i.1 (m i.1 - 1))) K := by
-- proof
  apply StatMech.Exact3D.copyDeleteEmbeddingDecrement_sources_map G m i K

/--
[copyDeletePreimageDecrement_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeletePreimageDecrement_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
-- given
  (j : {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i}) :
-- imply
  (copyDeletePreimageDecrement G m i j).1 = j.1.1 := by
-- proof
  apply StatMech.Exact3D.copyDeletePreimageDecrement_fst G m i j

/--
[copyDeletePreimageDecrement_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeletePreimageDecrement_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
-- given
  (j : {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i}) :
-- imply
  Sharpness.FluxEdgeCopy.endsM G (Function.update m i.1 (m i.1 - 1)) (copyDeletePreimageDecrement G m i j) = Sharpness.FluxEdgeCopy.endsM G m j.1 := by
-- proof
  apply StatMech.Exact3D.copyDeletePreimageDecrement_ends G m i j

/--
[copyDeleteEmbeddingDecrement_preimage_rightInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeleteEmbeddingDecrement_preimage_rightInverse_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m} :
-- imply
  Function.RightInverse (copyDeletePreimageDecrement G m i) (copyDeleteEmbeddingDecrement G m i) := by
-- proof
  apply StatMech.Exact3D.copyDeleteEmbeddingDecrement_preimage_rightInverse G m i

/--
[copyDeletePreimageDecrement_embedding_leftInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeletePreimageDecrement_embedding_leftInverse_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m} :
-- imply
  Function.LeftInverse (copyDeletePreimageDecrement G m i) (copyDeleteEmbeddingDecrement G m i) := by
-- proof
  apply StatMech.Exact3D.copyDeletePreimageDecrement_embedding_leftInverse G m i

/--
[copyDeleteEmbeddingDecrementFinset_preimageErase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeleteEmbeddingDecrementFinset_preimageErase_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)} :
-- imply
  copyDeleteEmbeddingDecrementFinset G m i (copyDeletePreimageDecrementEraseFinset G m i K) = K.erase i := by
-- proof
  apply StatMech.Exact3D.copyDeleteEmbeddingDecrementFinset_preimageErase G m i K

/--
[copyDeletePreimageDecrementErase_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeletePreimageDecrementErase_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)} :
-- imply
  (copyDeletePreimageDecrementEraseFinset G m i K).card = (K.erase i).card := by
-- proof
  apply StatMech.Exact3D.copyDeletePreimageDecrementErase_card G m i K

/--
[copyDeletePreimageDecrementEraseFinset_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeletePreimageDecrementEraseFinset_univ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m} :
-- imply
  copyDeletePreimageDecrementEraseFinset G m i (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1)))) := by
-- proof
  apply StatMech.Exact3D.copyDeletePreimageDecrementEraseFinset_univ G m i

/--
[copyDeletePreimageDecrementErase_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma copyDeletePreimageDecrementErase_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy G m}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy G m)} :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G (Function.update m i.1 (m i.1 - 1))) (copyDeletePreimageDecrementEraseFinset G m i K) = Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM G m) (K.erase i) := by
-- proof
  apply StatMech.Exact3D.copyDeletePreimageDecrementErase_sources G m i K

/--
[finiteBoundaryGhostBoundaryCrossingCopyCount_le_boundaryGhostMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingCopyCount_le_boundaryGhostMultiplicity_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)} :
-- imply
  finiteBoundaryGhostBoundaryCrossingCopyCount m v K ≤ m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingCopyCount_le_boundaryGhostMultiplicity m v K

/--
[finiteBoundaryGhostBoundaryCrossingPairCount_le_sourceSector_card_mul_boundaryGhostMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairCount_le_sourceSector_card_mul_boundaryGhostMultiplicity_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostBoundaryCrossingPairCount m v ≤ (finiteBoundaryGhostSourceSector m).card * m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairCount_le_sourceSector_card_mul_boundaryGhostMultiplicity m v

/--
[finiteBoundaryGhost_collapsedSourceSector_has_boundaryGhostCrossingCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_collapsedSourceSector_has_boundaryGhostCrossingCopy_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hsector : 0 < (finiteBoundaryGhostSourceSector m).card)
  (hweight : Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
-- imply
  ∃ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v ∧ ∃ K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m), K ∈ finiteBoundaryGhostSourceSector m ∧ (∃ i ∈ K, some v ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧ none ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i) ∧ Sharpness.RandomCurrent.connK (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K (some (IsingFK.boxOrigin 3 n)) (some v) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_collapsedSourceSector_has_boundaryGhostCrossingCopy m hsector hweight

/--
[finiteBoundaryGhost_sources_remove_boundaryGhostCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sources_remove_boundaryGhostCopy_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
  {v : FK.boxVerts 3 n}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m}
-- given
  (hiK : i ∈ K)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = finiteBoundaryGhostOnePointSource 3 n)
  (hends : Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (K \ {i}) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sources_remove_boundaryGhostCopy m K hiK hsrc hends

/--
[finiteBoundaryGhost_sources_insert_boundaryGhostCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sources_insert_boundaryGhostCopy_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
  {v : FK.boxVerts 3 n}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m}
-- given
  (hiK : i ∉ K)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))
  (hends : Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (insert i K) = finiteBoundaryGhostOnePointSource 3 n := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sources_insert_boundaryGhostCopy m K hiK hsrc hends

/--
[finiteBoundaryGhost_sources_remove_boundaryGhostCopy_from_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sources_remove_boundaryGhostCopy_from_twoPoint_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
  {v : FK.boxVerts 3 n}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m}
-- given
  (hiK : i ∈ K)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))
  (hends : Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (K \ {i}) = finiteBoundaryGhostOnePointSource 3 n := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sources_remove_boundaryGhostCopy_from_twoPoint m K hiK hsrc hends

/--
[finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
  {v : FK.boxVerts 3 n}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m}
-- given
  (hiK : i ∈ K)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = finiteBoundaryGhostOnePointSource 3 n)
  (hends : Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1))) (copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) m i K) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy m K hiK hsrc hends

/--
[finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy_from_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy_from_twoPoint_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
  {v : FK.boxVerts 3 n}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m}
-- given
  (hiK : i ∈ K)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) K = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))
  (hends : Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1))) (copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) m i K) = finiteBoundaryGhostOnePointSource 3 n := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy_from_twoPoint m K hiK hsrc hends

/--
[finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m}
-- given
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n)
  (hends : Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1))) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1)))) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy m hsrc hends

/--
[finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy_eq_fullSource_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy_eq_fullSource_symmDiff_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m}
-- given
  (hends : Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1))) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1)))) = Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ∆ ({some v, none} : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy_eq_fullSource_symmDiff m hends

/--
[finiteBoundaryGhostFullSourceOnePoint_of_decremented_univ_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostFullSourceOnePoint_of_decremented_univ_source_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m}
-- given
  (hends : Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none))
  (hdec : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1))) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1)))) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :
-- imply
  finiteBoundaryGhostFullSourceOnePoint n m := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostFullSourceOnePoint_of_decremented_univ_source m hends hdec

/--
[finiteBoundaryGhostBoundaryCrossingSourceSector_exists_removedSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingSourceSector_exists_removedSource_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hK : K ∈ finiteBoundaryGhostBoundaryCrossingSourceSector m v) :
-- imply
  ∃ i ∈ K, some v ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧ none ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧ Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (K \ {i}) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingSourceSector_exists_removedSource m hK

/--
[finiteBoundaryGhostBoundaryCrossingSourceSector_exists_decrementedRemovedSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingSourceSector_exists_decrementedRemovedSource_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hK : K ∈ finiteBoundaryGhostBoundaryCrossingSourceSector m v) :
-- imply
  ∃ i ∈ K, some v ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧ none ∈ Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧ Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1))) (copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) m i K) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingSourceSector_exists_decrementedRemovedSource m hK

/--
[finiteBoundaryGhostBoundaryCrossingPairs_decremented_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_decremented_source_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) (copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_decremented_source m v hp

/--
[finiteBoundaryGhostBoundaryCrossingPairs_decremented_univ_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_decremented_univ_source_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1)))) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_decremented_univ_source m v hp hsrc

/--
[finiteBoundaryGhostBoundaryCrossingPairs_decremented_univ_source_eq_fullSource_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_decremented_univ_source_eq_fullSource_symmDiff_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1)))) = Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ∆ ({some v, none} : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_decremented_univ_source_eq_fullSource_symmDiff m v hp

/--
[finiteBoundaryGhostBoundaryCrossingPairs_fullSourceOnePoint_of_decremented_univ_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_fullSourceOnePoint_of_decremented_univ_source_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v)
  (hdec : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1)))) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :
-- imply
  finiteBoundaryGhostFullSourceOnePoint n m := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_fullSourceOnePoint_of_decremented_univ_source m v hp hdec

/--
[finiteBoundaryGhostBoundaryCrossingPairs_inactive_decremented_univ_source_ne_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_inactive_decremented_univ_source_ne_twoPoint_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v)
  (hinactive : ¬ finiteBoundaryGhostFullSourceOnePoint n m) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1)))) ≠ (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_inactive_decremented_univ_source_ne_twoPoint m v hp hinactive

/--
[finiteBoundaryGhostBoundaryCrossingPairs_decremented_mem_twoPointSourceSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_decremented_mem_twoPointSourceSector_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1 ∈ finiteBoundaryGhostTwoPointSourceSector (Function.update m p.2.1 (m p.2.1 - 1)) v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_decremented_mem_twoPointSourceSector m v hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementData_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementData_fst_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairDecrementData m v hp).1 = Function.update m p.2.1 (m p.2.1 - 1) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementData_fst m v hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementData_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementData_snd_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairDecrementData m v hp).2.1 = copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementData_snd m v hp

/--
[finiteBoundaryGhostBoundaryCrossingPairFullSourceClassifiedDecrementData_toSourceData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairFullSourceClassifiedDecrementData_toSourceData_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairFullSourceClassifiedDecrementData m v hp).toSourceData = finiteBoundaryGhostBoundaryCrossingPairDecrementData m v hp := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairFullSourceClassifiedDecrementData_toSourceData m v hp

/--
[finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData_toSourceData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData_toSourceData_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n)
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData m v hsrc hp).toSourceData = finiteBoundaryGhostBoundaryCrossingPairDecrementData m v hp := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData_toSourceData m v hsrc hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementImage_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementImage_mem_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v} :
-- imply
  d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v ↔ ∃ p, ∃ hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, finiteBoundaryGhostBoundaryCrossingPairDecrementData m v hp = d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementImage_mem m v d

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementImage_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementImage_card_le_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v).card ≤ (finiteBoundaryGhostBoundaryCrossingPairs m v).card := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementImage_card_le m v

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
-- given
  (p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}) :
-- imply
  p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d ↔ finiteBoundaryGhostBoundaryCrossingPairDecrementData (p := p.1) m v p.2 = d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem m v d p

/--
[finiteBoundaryGhostBoundaryCrossingPair_selectedCopy_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPair_selectedCopy_edge_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}) :
-- imply
  p.1.2.1 = ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPair_selectedCopy_edge m v p

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_selectedCopy_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_selectedCopy_edge_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
-- given
  (_hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
-- imply
  p.1.2.1 = ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_selectedCopy_edge m v d _hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_eq_of_selectedCopy_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_eq_of_selectedCopy_eq_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {p q : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d)
  (hq : q ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d)
  (hcopy : p.1.2 = q.1.2) :
-- imply
  p = q := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_eq_of_selectedCopy_eq m v d hp hq hcopy

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v} :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card ≤ m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_boundaryGhostMultiplicity m v d

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_card_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairs m v).card = ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v, (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_card m v

/--
[finset_sum_attach_image_fiber_weight_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finset_sum_attach_image_fiber_weight_nsmul_eq
  [DecidableEq β]
  [AddCommMonoid M]
  {S : Finset α}
  {W : β → M}
-- given
  (f : {x // x ∈ S} → β) :
-- imply
  (∑ x ∈ S.attach, W (f x)) = ∑ y ∈ S.attach.image f, (S.attach.filter (fun x => f x = y)).card • W y := by
-- proof
  apply StatMech.Exact3D.finset_sum_attach_image_fiber_weight_nsmul S f W

/--
[finset_sum_image_fiber_card_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finset_sum_image_fiber_card_mul_eq
  [DecidableEq β]
  {S : Finset α}
  {f : α → β}
  {W : β → ℝ} :
-- imply
  Finset.sum S (fun x => W (f x)) = Finset.sum (S.image f) (fun y => ((S.filter (fun x => f x = y)).card : ℝ) * W y) := by
-- proof
  apply StatMech.Exact3D.finset_sum_image_fiber_card_mul S f W

/--
[finset_sum_mul_le_const_mul_sum_of_le_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finset_sum_mul_le_const_mul_sum_of_le_nonneg_eq
  {S : Finset α}
  {C W : α → ℝ}
  {M : ℝ}
-- given
  (hC : ∀ x, x ∈ S → C x ≤ M)
  (hW : ∀ x, x ∈ S → 0 ≤ W x) :
-- imply
  (∑ x ∈ S, C x * W x) ≤ M * ∑ x ∈ S, W x := by
-- proof
  apply StatMech.Exact3D.finset_sum_mul_le_const_mul_sum_of_le_nonneg S C W hC hW

/--
[finset_sum_le_subtype_sum_of_inactive_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finset_sum_le_subtype_sum_of_inactive_nonpos_eq
  {S : Finset α}
  [DecidablePred p]
  {F : α → ℝ}
  {G : {a // p a} → ℝ}
-- given
  (p : α → Prop)
  (hnot : ∀ a, a ∈ S → ¬ p a → F a ≤ 0)
  (hle : ∀ a, a ∈ S → (ha : p a) → F a ≤ G ⟨a, ha⟩) :
-- imply
  Finset.sum S F ≤ Finset.sum (Finset.subtype p S) G := by
-- proof
  apply StatMech.Exact3D.finset_sum_le_subtype_sum_of_inactive_nonpos S p F G hnot hle

/--
[mem_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma mem_fiber_eq
  {I : FinsetFiberIndex β}
  {b : β}
  {a : I.α} :
-- imply
  a ∈ I.fiber b ↔ a ∈ I.domain ∧ I.map a = b := by
-- proof
  apply StatMech.Exact3D.FinsetFiberIndex.mem_fiber I b a

/--
[mem_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma mem_image_eq
  {I : FinsetFiberIndex β}
  {b : β} :
-- imply
  b ∈ I.image ↔ ∃ a, a ∈ I.domain ∧ I.map a = b := by
-- proof
  apply StatMech.Exact3D.FinsetFiberIndex.mem_image I b

/--
[image_card_le_domain_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma image_card_le_domain_card_eq
  {I : FinsetFiberIndex β} :
-- imply
  (I.image.card : ℝ) ≤ (I.domain.card : ℝ) := by
-- proof
  apply StatMech.Exact3D.FinsetFiberIndex.image_card_le_domain_card I

/--
[sum_fiber_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sum_fiber_weight_eq
  {I : FinsetFiberIndex β}
  {W : β → ℝ} :
-- imply
  Finset.sum I.domain (fun a => W (I.map a)) = Finset.sum I.image (fun b => ((I.fiber b).card : ℝ) * W b) := by
-- proof
  apply StatMech.Exact3D.FinsetFiberIndex.sum_fiber_weight I W

/--
[sum_le_const_mul_image_sum_of_fiber_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sum_le_const_mul_image_sum_of_fiber_card_le_eq
  {I : FinsetFiberIndex β}
  {W : β → ℝ}
  {B : ℝ}
-- given
  (hcard : ∀ b, b ∈ I.image → ((I.fiber b).card : ℝ) ≤ B)
  (hW : ∀ b, b ∈ I.image → 0 ≤ W b) :
-- imply
  Finset.sum I.domain (fun a => W (I.map a)) ≤ B * Finset.sum I.image W := by
-- proof
  apply StatMech.Exact3D.FinsetFiberIndex.sum_le_const_mul_image_sum_of_fiber_card_le I W hcard hW

/--
[image_sum_le_image_sum_mul_of_fiber_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma image_sum_le_image_sum_mul_of_fiber_card_le_eq
  {I : FinsetFiberIndex β}
  {W C : β → ℝ}
-- given
  (hcard : ∀ b, b ∈ I.image → ((I.fiber b).card : ℝ) ≤ C b)
  (hW : ∀ b, b ∈ I.image → 0 ≤ W b) :
-- imply
  Finset.sum I.image (fun b => ((I.fiber b).card : ℝ) * W b) ≤ Finset.sum I.image (fun b => C b * W b) := by
-- proof
  apply StatMech.Exact3D.FinsetFiberIndex.image_sum_le_image_sum_mul_of_fiber_card_le I W C hcard hW

/--
[sum_le_image_sum_mul_of_fiber_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma sum_le_image_sum_mul_of_fiber_card_le_eq
  {I : FinsetFiberIndex β}
  {W C : β → ℝ}
-- given
  (hcard : ∀ b, b ∈ I.image → ((I.fiber b).card : ℝ) ≤ C b)
  (hW : ∀ b, b ∈ I.image → 0 ≤ W b) :
-- imply
  Finset.sum I.domain (fun a => W (I.map a)) ≤ Finset.sum I.image (fun b => C b * W b) := by
-- proof
  apply StatMech.Exact3D.FinsetFiberIndex.sum_le_image_sum_mul_of_fiber_card_le I W C hcard hW

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_weight_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {W : finiteBoundaryGhostTwoPointSourceData n v → ℝ} :
-- imply
  Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain (fun a => W ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a)) = Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).image (fun d => (((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).fiber d).card : ℝ) * W d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_weight m v W

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain (fun a => finiteBoundaryGhostTwoPointSourceDataWeight β H ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a)) = Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).image (fun d => (((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).fiber d).card : ℝ) * finiteBoundaryGhostTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_fiber_dataWeight m v

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_dataWeight_le_boundaryGhostMultiplicity_mul_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_dataWeight_le_boundaryGhostMultiplicity_mul_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain (fun a => finiteBoundaryGhostTwoPointSourceDataWeight β H ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a)) ≤ (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).image (fun d => finiteBoundaryGhostTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_sum_dataWeight_le_boundaryGhostMultiplicity_mul_image_sum hβ hH m v

/--
[finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  Finset.sum (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).domain (fun a => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).map a)) = Finset.sum (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).image (fun d => (((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).fiber d).card : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_dataWeight m v hsrc

/--
[finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_fiber_card_le_boundaryGhostMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostCollapsedTwoPointSourceData n v}
-- given
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  ((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).fiber d).card ≤ m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_fiber_card_le_boundaryGhostMultiplicity m v hsrc d

/--
[finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_dataWeight_le_boundaryGhostMultiplicity_mul_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_dataWeight_le_boundaryGhostMultiplicity_mul_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  Finset.sum (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).domain (fun a => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).map a)) ≤ (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * Finset.sum (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).image (fun d => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_dataWeight_le_boundaryGhostMultiplicity_mul_image_sum hβ hH m v hsrc

/--
[finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_weight_le_boundaryGhostMultiplicity_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_weight_le_boundaryGhostMultiplicity_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  Finset.sum (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).image (fun d => (((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).fiber d).card : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤ ∑ d ∈ (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).image, (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex_sum_fiber_weight_le_boundaryGhostMultiplicity_sum hβ hH m v hsrc

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_image_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_image_eq_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).image = finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_image_eq m v

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_fiber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_fiber_eq_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v} :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).fiber d = finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementIndex_fiber_eq m v d

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_dataWeight_indexDomain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_dataWeight_indexDomain_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain (fun a => finiteBoundaryGhostTwoPointSourceDataWeight β H ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a)) = Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v) (fun d => ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card : ℝ) * finiteBoundaryGhostTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_dataWeight_indexDomain m v

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v p = finiteBoundaryGhostTwoPointSourceDataWeight β H (finiteBoundaryGhostBoundaryCrossingPairDecrementData (p := p) m v hp) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_dataWeight m hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeightSum_eq_indexDomain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeightSum_eq_indexDomain_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v) (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v) = Finset.sum ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).domain) (fun a => finiteBoundaryGhostTwoPointSourceDataWeight β H ((finiteBoundaryGhostBoundaryCrossingPairDecrementIndex m v).map a)) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeightSum_eq_indexDomain m v

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_card_le_boundaryGhostMultiplicity_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_card_le_boundaryGhostMultiplicity_sum_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v, (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card) ≤ ∑ _d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v, m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_card_le_boundaryGhostMultiplicity_sum m v

/--
[finiteBoundaryGhostBoundaryCrossingPairs_card_le_decrementImage_card_mul_boundaryGhostMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_card_le_decrementImage_card_mul_boundaryGhostMultiplicity_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairs m v).card ≤ (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v).card * m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_card_le_decrementImage_card_mul_boundaryGhostMultiplicity m v

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_weight_le_boundaryGhostMultiplicity_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_weight_le_boundaryGhostMultiplicity_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v, ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card : ℝ) * finiteBoundaryGhostTwoPointSourceDataWeight β H d) ≤ ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v, (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementImage_sum_fiber_weight_le_boundaryGhostMultiplicity_sum hβ hH m v

/--
[finiteBoundaryGhost_weight_decrement_boundaryGhostCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhost_weight_decrement_boundaryGhostCopy_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m}
-- given
  (hvbdry : FK.boxBoundary 3 n v)
  (hends : Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
-- imply
  ((m i.1 : ℝ) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m i.1 (m i.1 - 1))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhost_weight_decrement_boundaryGhostCopy m hvbdry hends

/--
[finiteBoundaryGhostBoundaryCrossingPairs_weight_decrement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_weight_decrement_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hvbdry : FK.boxBoundary 3 n v)
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  ((m p.2.1 : ℝ) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_weight_decrement m hvbdry hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_zero_of_weight_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_zero_of_weight_eq_zero_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hvbdry : FK.boxBoundary 3 n v)
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v)
  (hweight : Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) = 0) :
-- imply
  finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v p = 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_eq_zero_of_weight_eq_zero hvbdry hp hweight

/--
[finiteBoundaryGhostBoundaryCrossingPairs_weight_le_decrement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_weight_le_decrement_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v)
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_weight_le_decrement hβ hH m hvbdry hp

/--
[finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_decrement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_decrement_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v)
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_decrement hβ hH m hvbdry hp

/--
[finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_collapsedDecrementDataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_collapsedDecrementDataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n)
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData m v hsrc hp) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_collapsedDecrementDataWeight hβ hH m hvbdry hsrc hp

/--
[finiteBoundaryGhostBoundaryCrossingPairs_summand_le_decremented_source_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairs_summand_le_decremented_source_summand_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v)
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
-- imply
  (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ (β * H) * ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) (copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1)))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairs_summand_le_decremented_source_summand hβ hH m hvbdry hp

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedPairWeightSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedPairWeightSum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ ∑ p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedPairWeightSum hβ hH m hvbdry

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourcePairWeightSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourcePairWeightSum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ ∑ p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (β * H) * ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1))) (copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update m p.2.1 (m p.2.1 - 1)))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourcePairWeightSum hβ hH m hvbdry

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourceWeightSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourceWeightSum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v) (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementedSourceWeightSum hβ hH m hvbdry

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementImage_sum_fiber_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementImage_sum_fiber_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ Finset.sum (finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v) (fun d => ((finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card : ℝ) * finiteBoundaryGhostTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_decrementImage_sum_fiber_dataWeight hβ hH m hvbdry

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_collapsedDecrementIndex_sum_fiber_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_collapsedDecrementIndex_sum_fiber_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ Finset.sum (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).image (fun d => (((finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).fiber d).card : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_collapsedDecrementIndex_sum_fiber_dataWeight hβ hH m hvbdry hsrc

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDecrementImage_sum_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDecrementImage_sum_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * ∑ d ∈ (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementIndex m v hsrc).image, finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDecrementImage_sum_dataWeight hβ hH m hvbdry hsrc

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDataWeight_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDataWeight_tsum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * ∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v, finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_collapsedDataWeight_tsum hβ hH m hvbdry hsrc

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v)
  (hsrc : Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * ((β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum hβ hH m hvbdry hsrc

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_decrementImage_sum_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_decrementImage_sum_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v, (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_decrementImage_sum_dataWeight hβ hH m hvbdry

/--
[finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v) :
-- imply
  (∑ _p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v, (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ≤ (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v, finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairSum_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight hβ hH m hvbdry

/--
[finiteBoundaryGhostSourceSector_subset_boundaryCrossing_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSourceSector_subset_boundaryCrossing_biUnion_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hweight : Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
-- imply
  finiteBoundaryGhostSourceSector m ⊆ (Finset.univ.filter (FK.boxBoundary 3 n)).biUnion (fun v => finiteBoundaryGhostBoundaryCrossingSourceSector m v) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostSourceSector_subset_boundaryCrossing_biUnion m hweight

/--
[finiteBoundaryGhostSourceSector_card_le_boundaryCrossing_card_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSourceSector_card_le_boundaryCrossing_card_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hweight : Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
-- imply
  ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostSourceSector_card_le_boundaryCrossing_card_sum m hweight

/--
[finiteBoundaryGhostCollapsedSummand_le_boundaryCrossingSummand_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSummand_le_boundaryCrossingSummand_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * ((finiteBoundaryGhostSourceSector m).card : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSummand_le_boundaryCrossingSummand_sum hβ hH m

/--
[finiteBoundaryGhostBoundaryCrossingSummand_le_crossingPairCountSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingSummand_le_crossingPairCountSummand_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingSummand_le_crossingPairCountSummand hβ hH m v

/--
[finiteBoundaryGhostCollapsedSummand_le_crossingPairCountSummand_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSummand_le_crossingPairCountSummand_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * ((finiteBoundaryGhostSourceSector m).card : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * (finiteBoundaryGhostBoundaryCrossingPairCount m v : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSummand_le_crossingPairCountSummand_sum hβ hH m

/--
[finiteBoundaryGhostBoundaryCrossingSummand_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingSummand_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v) :
-- imply
  ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v, finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingSummand_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight hβ hH m hvbdry

/--
[finiteBoundaryGhostBoundaryCrossingSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hvbdry : FK.boxBoundary 3 n v) :
-- imply
  ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * ((finiteBoundaryGhostBoundaryCrossingSourceSector m v).card : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * ((β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum hβ hH m hvbdry

/--
[finiteBoundaryGhostCollapsedSummand_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSummand_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * ((finiteBoundaryGhostSourceSector m).card : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * ∑ d ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementImage m v, finiteBoundaryGhostTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSummand_le_boundaryGhostMultiplicity_mul_decrementImage_sum_dataWeight_sum hβ hH m

/--
[finiteBoundaryGhostCollapsedSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  ((if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * ((finiteBoundaryGhostSourceSector m).card : ℝ)) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ) * ((β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSummand_le_boundaryGhostMultiplicity_mul_emptyCollapsedSum_sum hβ hH m

/--
[finiteBoundaryGhostWeightNonzeroCutoff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostWeightNonzeroCutoff_mem_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ} :
-- imply
  m ∈ finiteBoundaryGhostWeightNonzeroCutoff β H n Ω ↔ m ∈ Ω ∧ Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostWeightNonzeroCutoff_mem

/--
[finiteBoundaryGhostWeightNonzeroCutoff_weight_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostWeightNonzeroCutoff_weight_ne_zero_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hm : m ∈ finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) :
-- imply
  Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostWeightNonzeroCutoff_weight_ne_zero hm

/--
[finiteBoundaryGhostWeightNonzeroCutoff_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostWeightNonzeroCutoff_subset_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostWeightNonzeroCutoff β H n Ω ⊆ Ω := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostWeightNonzeroCutoff_subset

/--
[finiteBoundaryGhostWeightNonzeroCutoff_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostWeightNonzeroCutoff_mono_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω Ω' : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hΩ : Ω ⊆ Ω') :
-- imply
  finiteBoundaryGhostWeightNonzeroCutoff β H n Ω ⊆ finiteBoundaryGhostWeightNonzeroCutoff β H n Ω' := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostWeightNonzeroCutoff_mono hΩ

/--
[finiteBoundaryGhostWeightNonzeroCutoff_filter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostWeightNonzeroCutoff_filter_eq_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  [DecidablePred P]
-- given
  (P : (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop) :
-- imply
  finiteBoundaryGhostWeightNonzeroCutoff β H n (Ω.filter P) = (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω).filter P := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostWeightNonzeroCutoff_filter_eq β H n Ω P

/--
[finiteBoundaryGhostWeightNonzeroCutoff_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostWeightNonzeroCutoff_idem_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostWeightNonzeroCutoff β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) = finiteBoundaryGhostWeightNonzeroCutoff β H n Ω := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostWeightNonzeroCutoff_idem β H n Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_eq_zero_of_weight_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_eq_zero_of_weight_eq_zero_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hweight : Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) = 0) :
-- imply
  finiteBoundaryGhostCollapsedSourceSummand β H n m = 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_eq_zero_of_weight_eq_zero m hweight

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_eq_weightNonzeroCutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_eq_weightNonzeroCutoff_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) = ∑ m ∈ finiteBoundaryGhostWeightNonzeroCutoff β H n Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_eq_weightNonzeroCutoff β H n Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostCollapsedSourceSummand β H n m := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_nonneg hβ hH m

/--
[finiteBoundaryGhostCollapsedSourceSummand_tsum_eq_emptyCollapsedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_tsum_eq_emptyCollapsedSum_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  (∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ, finiteBoundaryGhostCollapsedSourceSummand β H n m) = edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_tsum_eq_emptyCollapsedSum β H n

/--
[finiteBoundaryGhostCollapsedSourceSummand_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_summable_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  Summable (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostCollapsedSourceSummand β H n m) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_summable β H n

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_emptyCollapsedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_emptyCollapsedSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_emptyCollapsedSum hβ hH Ω

/--
[tsum_le_of_all_finset_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma tsum_le_of_all_finset_sum_le_eq
  {f : α → ℝ}
  {C : ℝ}
-- given
  (hf : Summable f)
  (h : ∀ Ω : Finset α, (∑ a ∈ Ω, f a) ≤ C) :
-- imply
  (∑' a, f a) ≤ C := by
-- proof
  apply StatMech.Exact3D.tsum_le_of_all_finset_sum_le hf h

/--
[finiteBoundaryGhostCollapsedSourceSummand_le_boundaryMultiplicityDenominatorSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_le_boundaryMultiplicityDenominatorSum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  finiteBoundaryGhostCollapsedSourceSummand β H n m ≤ finiteBoundaryGhostBoundaryMultiplicityDenominatorSum β H n m := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_le_boundaryMultiplicityDenominatorSum hβ hH m

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityDenominatorSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityDenominatorSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ m ∈ Ω, finiteBoundaryGhostBoundaryMultiplicityDenominatorSum β H n m := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityDenominatorSum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), (∑ m ∈ Ω, (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ)) * ((β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_emptyCollapsedSum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedTwoPointDenominator_eq_currentSum_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedTwoPointDenominator_eq_currentSum_mul_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) = Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) * Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedTwoPointDenominator_eq_currentSum_mul β H n v

/--
[finiteBoundaryGhostCollapsedTwoPointDenominator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedTwoPointDenominator_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedTwoPointDenominator_nonneg hβ hH n v

/--
[finiteBoundaryGhostBoundaryEdge_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryEdge_coupling_eq
  {H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : FK.boxBoundary 3 n v) :
-- imply
  boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) (finiteBoundaryGhostBoundaryEdge n v).1 = H := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryEdge_coupling H hv

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_current_eq_update_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_current_eq_update_target_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
-- imply
  m = Function.update d.1 (finiteBoundaryGhostBoundaryEdge n v) (d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_current_eq_update_target m v d hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_eq_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_eq_succ_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
-- imply
  m (finiteBoundaryGhostBoundaryEdge n v) = d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_eq_succ m v d hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_le_one_iff_target_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_le_one_iff_target_zero_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
-- imply
  m (finiteBoundaryGhostBoundaryEdge n v) ≤ (1 : ℕ) ↔ d.1 (finiteBoundaryGhostBoundaryEdge n v) = 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_oldBoundaryGhostMultiplicity_le_one_iff_target_zero m v d hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_not_oldBoundaryGhostMultiplicity_le_one_iff_target_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_not_oldBoundaryGhostMultiplicity_le_one_iff_target_pos_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v}}
-- given
  (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d) :
-- imply
  ¬ m (finiteBoundaryGhostBoundaryEdge n v) ≤ (1 : ℕ) ↔ 0 < d.1 (finiteBoundaryGhostBoundaryEdge n v) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_not_oldBoundaryGhostMultiplicity_le_one_iff_target_pos m v d hp

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_decrementedBoundaryGhostMultiplicity_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_decrementedBoundaryGhostMultiplicity_succ_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v} :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card ≤ d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_le_decrementedBoundaryGhostMultiplicity_succ m v d

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_currentSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_currentSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), (∑ m ∈ Ω, (m ⟨s(some v, none), by rw [SimpleGraph.mem_edgeFinset] simp [Sharpness.withGhost]⟩ : ℝ)) * ((β * H) * (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) * Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryMultiplicityProfile_mul_currentSum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryWeightedProfileCurrentSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryWeightedProfileCurrentSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), ∑ m ∈ Ω, (m (finiteBoundaryGhostBoundaryEdge n v) : ℝ) * ((β * boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) (finiteBoundaryGhostBoundaryEdge n v).1) * (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) * Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryWeightedProfileCurrentSum_sum hβ hH Ω

/--
[finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_boundary_sum_vertexCutoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_boundary_sum_vertexCutoffSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω = ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_boundary_sum_vertexCutoffSum β H n Ω

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m) => Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
-- imply
  0 ≤ finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v p := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_nonneg hβ hH m v p

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {p : finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand β H n m v p := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand_nonneg hβ hH m v p

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
-- imply
  0 ≤ finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_nonneg hβ hH a

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_decremented_univ_source_ne_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_decremented_univ_source_ne_twoPoint_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))
  (hinactive : ¬ finiteBoundaryGhostFullSourceOnePoint n a.1) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData n v a).1) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData n v a).1)) ≠ (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_decremented_univ_source_ne_twoPoint a hinactive

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigma_decremented_univ_source_eq_fullSource_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigma_decremented_univ_source_eq_fullSource_symmDiff_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData n v a).1) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData n v a).1)) = Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) a.1) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)) ∆ ({some v, none} : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigma_decremented_univ_source_eq_fullSource_symmDiff a

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData_toSourceData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData_toSourceData_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
-- imply
  (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData n v a).toSourceData = finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData n v a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData_toSourceData a

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_eq_fullSourceClassifiedDataWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_eq_fullSourceClassifiedDataWeight_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a = finiteBoundaryGhostFullSourceClassifiedTwoPointSourceDataWeight β H (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaFullSourceClassifiedDecrementData n v a) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_eq_fullSourceClassifiedDataWeight a

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_fullSourceClass_ne_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_fullSourceClass_ne_twoPoint_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))
  (hinactive : ¬ finiteBoundaryGhostFullSourceOnePoint n a.1) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) a.1) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) a.1)) ∆ ({some v, none} : Finset (Option (FK.boxVerts 3 n))) ≠ (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigma_inactive_fullSourceClass_ne_twoPoint a hinactive

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigma_mem_decrementFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigma_mem_decrementFiber_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
-- imply
  a.2 ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber a.1 v (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData n v a) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigma_mem_decrementFiber a

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigma_currentMultiplicity_le_one_iff_decrementData_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigma_currentMultiplicity_le_one_iff_decrementData_zero_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
-- imply
  a.1 (finiteBoundaryGhostBoundaryEdge n v) ≤ (1 : ℕ) ↔ (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData n v a).1 (finiteBoundaryGhostBoundaryEdge n v) = 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigma_currentMultiplicity_le_one_iff_decrementData_zero a

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigma_not_currentMultiplicity_le_one_iff_decrementData_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigma_not_currentMultiplicity_le_one_iff_decrementData_pos_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
-- imply
  ¬ a.1 (finiteBoundaryGhostBoundaryEdge n v) ≤ (1 : ℕ) ↔ 0 < (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaDecrementData n v a).1 (finiteBoundaryGhostBoundaryEdge n v) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigma_not_currentMultiplicity_le_one_iff_decrementData_pos a

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_eq_collapsedDataWeight_of_fullSourceOnePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_eq_collapsedDataWeight_of_fullSourceOnePoint_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))
  (hsrc : finiteBoundaryGhostFullSourceOnePoint n a.1) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a = finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H (finiteBoundaryGhostBoundaryCrossingPairCollapsedDecrementData a.1 v (by simpa [finiteBoundaryGhostFullSourceOnePoint] using hsrc) a.2.2) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_eq_collapsedDataWeight_of_fullSourceOnePoint a hsrc

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_nonneg hβ hH Ω v

/--
[finiteBoundaryGhostDecrementedSourceWeightSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightSummand_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostDecrementedSourceWeightSummand β H n m := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightSummand_nonneg hβ hH m

/--
[finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω = ∑ m ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightSummand β H n m := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand β H n Ω

/--
[finiteBoundaryGhostDecrementedSourceWeightCutoffSum_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightCutoffSum_mono_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω Ω' : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hΩ : Ω ⊆ Ω') :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω ≤ finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω' := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightCutoffSum_mono hβ hH hΩ

/--
[finiteBoundaryGhostDecrementedSourceWeightCutoffSum_filter_add_filter_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightCutoffSum_filter_add_filter_not_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  [DecidablePred P]
-- given
  (P : (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω = finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n (Ω.filter P) + finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n (Ω.filter fun m => ¬ P m) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightCutoffSum_filter_add_filter_not β H n Ω P

/--
[finiteBoundaryGhostDecrementedSourceWeightCutoffSum_le_of_filter_le_filter_not_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightCutoffSum_le_of_filter_le_filter_not_le_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  [DecidablePred P]
  {A B C : ℝ}
-- given
  (P : (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop)
  (hP : finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n (Ω.filter P) ≤ A)
  (hnot : finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n (Ω.filter fun m => ¬ P m) ≤ B)
  (hAB : A + B ≤ C) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω ≤ C := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightCutoffSum_le_of_filter_le_filter_not_le β H n Ω P hP hnot hAB

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_mono_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω Ω' : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hΩ : Ω ⊆ Ω') :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤ finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω' v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_mono hβ hH hΩ v

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_add_filter_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_add_filter_not_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  [DecidablePred P]
-- given
  (P : (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v = finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (Ω.filter P) v + finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (Ω.filter fun m => ¬ P m) v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_add_filter_not β H n Ω v P

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_filter_le_filter_not_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_filter_le_filter_not_le_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  [DecidablePred P]
  {A B C : ℝ}
-- given
  (P : (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → Prop)
  (hP : finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (Ω.filter P) v ≤ A)
  (hnot : finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (Ω.filter fun m => ¬ P m) v ≤ B)
  (hAB : A + B ≤ C) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤ C := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_filter_le_filter_not_le β H n Ω v P hP hnot hAB

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_sum_eq_zero_of_weight_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_sum_eq_zero_of_weight_eq_zero_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvbdry : FK.boxBoundary 3 n v)
  (hweight : Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) = 0) :
-- imply
  Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v) (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v) = 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight_sum_eq_zero_of_weight_eq_zero hvbdry hweight

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_weightNonzeroCutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_weightNonzeroCutoff_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hvbdry : FK.boxBoundary 3 n v) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v = finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_weightNonzeroCutoff β H n Ω hvbdry

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_label_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_label_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  [Fintype ι]
  [DecidableEq ι]
  {label : (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → ι} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v = ∑ i : ι, finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (Ω.filter fun m => label m = i) v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_label_sum β H n Ω v label

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_label_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_label_sum_le_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  [Fintype ι]
  [DecidableEq ι]
  {label : (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → ι}
  {A : ι → ℝ}
  {C : ℝ}
-- given
  (hcase : ∀ i, finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (Ω.filter fun m => label m = i) v ≤ A i)
  (hC : (∑ i, A i) ≤ C) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤ C := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_label_sum_le β H n Ω v label hcase hC

/--
[finiteBoundaryGhostDecrementedSourceWeightCutoffSum_le_of_vertexCutoffSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightCutoffSum_le_of_vertexCutoffSum_le_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {A : FK.boxVerts 3 n → ℝ}
  {C : ℝ}
-- given
  (hA : ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) → finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤ A v)
  (hC : (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), A v) ≤ C) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω ≤ C := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightCutoffSum_le_of_vertexCutoffSum_le β H n Ω hA hC

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_mem_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (a : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)) :
-- imply
  a ∈ finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport n Ω v ↔ a.1 ∈ Ω := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_mem Ω v a

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexFiber_univ_sum_eq_pair_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexFiber_univ_sum_eq_pair_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  (∑ p : finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v, finiteBoundaryGhostDecrementedSourceWeightVertexFiberSummand β H n m v p) = Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m v) (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexFiber_univ_sum_eq_pair_sum β H m v

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_attach_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_attach_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v = ∑ m ∈ Ω.attach, Finset.sum (finiteBoundaryGhostBoundaryCrossingPairs m.1 v) (finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m.1 v) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_attach_sum β H n Ω v

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  (∑ a ∈ finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport n Ω v, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) = finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum β H n Ω v

/--
[finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight_nonneg hβ hH D

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  (∑ a ∈ finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport n Ω v, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) = Finset.sum (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).domain (fun a => finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).map a)) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum Ω v

/--
[finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum_eq_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum_eq_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  Finset.sum (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).domain (fun a => finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).map a)) = ∑ D ∈ (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).image, (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).fiber D).card : ℝ) * finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum_eq_image_sum Ω v

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  (∑ a ∈ finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport n Ω v, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) = ∑ D ∈ (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).image, (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).fiber D).card : ℝ) * finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum Ω v

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v = ∑ D ∈ (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).image, (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).fiber D).card : ℝ) * finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum Ω v

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_currentSupport_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_currentSupport_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (Ω : Finset (Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))) :
-- imply
  (∑ a ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) ≤ ∑ a ∈ finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport n (Ω.image Sigma.fst) v, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_currentSupport_sum hβ hH Ω

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_vertexCutoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_vertexCutoffSum_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (Ω : Finset (Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))) :
-- imply
  (∑ a ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) ≤ finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (Ω.image Sigma.fst) v := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_vertexCutoffSum hβ hH Ω

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_mono_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {Ω Ω' : Finset (Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hΩ : Ω ⊆ Ω') :
-- imply
  (∑ a ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) ≤ ∑ a ∈ Ω', finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_mono hβ hH hΩ

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_filter_add_filter_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_filter_add_filter_not_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  [DecidablePred P]
-- given
  (Ω : Finset (Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)))
  (P : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → Prop) :
-- imply
  (∑ a ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) = (∑ a ∈ Ω.filter P, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) + ∑ a ∈ Ω.filter (fun a => ¬ P a), finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_filter_add_filter_not β H Ω P

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_filter_le_filter_not_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_filter_le_filter_not_le_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  [DecidablePred P]
  {A B C : ℝ}
-- given
  (Ω : Finset (Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)))
  (P : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → Prop)
  (hP : (∑ a ∈ Ω.filter P, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) ≤ A)
  (hnot : (∑ a ∈ Ω.filter (fun a => ¬ P a), finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) ≤ B)
  (hAB : A + B ≤ C) :
-- imply
  (∑ a ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) ≤ C := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_filter_le_filter_not_le β H Ω P hP hnot hAB

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_eq_label_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_eq_label_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  [Fintype ι]
  [DecidableEq ι]
-- given
  (Ω : Finset (Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)))
  (label : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → ι) :
-- imply
  (∑ a ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) = ∑ i : ι, ∑ a ∈ Ω.filter (fun a => label a = i), finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_eq_label_sum β H Ω label

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_label_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_label_sum_le_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  [Fintype ι]
  [DecidableEq ι]
  {A : ι → ℝ}
  {C : ℝ}
-- given
  (Ω : Finset (Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)))
  (label : Sigma (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ => finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → ι)
  (hcase : ∀ i, (∑ a ∈ Ω.filter (fun a => label a = i), finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) ≤ A i)
  (hC : (∑ i, A i) ≤ C) :
-- imply
  (∑ a ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand β H n v a) ≤ C := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_label_sum_le β H Ω label hcase hC

/--
[finiteBoundaryGhostDecrementedSourceWeightFiberSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightFiberSummand_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {a : finiteBoundaryGhostDecrementedSourceWeightFiber n m}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostDecrementedSourceWeightFiberSummand β H n m a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightFiberSummand_nonneg hβ hH m a

/--
[finiteBoundaryGhostDecrementedSourceWeightSummand_eq_tsum_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightSummand_eq_tsum_fiber_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightSummand β H n m = ∑' a : finiteBoundaryGhostDecrementedSourceWeightFiber n m, finiteBoundaryGhostDecrementedSourceWeightFiberSummand β H n m a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightSummand_eq_tsum_fiber β H n m

/--
[finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {a : Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_nonneg hβ hH a

/--
[finiteBoundaryGhostDecrementedSourceWeightFiber_tsum_eq_boundary_pair_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightFiber_tsum_eq_boundary_pair_tsum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ} :
-- imply
  (∑' a : finiteBoundaryGhostDecrementedSourceWeightFiber n m, finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n ⟨m, a⟩) = ∑' v : {v : FK.boxVerts 3 n // v ∈ Finset.univ.filter (FK.boxBoundary 3 n)}, ∑' p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v.1}, finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v.1 p.1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightFiber_tsum_eq_boundary_pair_tsum β H n m

/--
[finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_tsum_eq_tsum_current_boundary_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_tsum_eq_tsum_current_boundary_pair_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hsum : Summable (finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n)) :
-- imply
  (∑' a : Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n), finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) = ∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ, ∑' v : {v : FK.boxVerts 3 n // v ∈ Finset.univ.filter (FK.boxBoundary 3 n)}, ∑' p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v.1}, finiteBoundaryGhostBoundaryCrossingPairDecrementedSourceWeight β H m v.1 p.1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_tsum_eq_tsum_current_boundary_pair hsum

/--
[finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_mem_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {a : Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n)} :
-- imply
  a ∈ finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport n Ω ↔ a.1 ∈ Ω := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_mem Ω a

/--
[finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_sum_eq_cutoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_sum_eq_cutoffSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  (∑ a ∈ finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport n Ω, finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) = finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport_sum_eq_cutoffSum β H n Ω

/--
[finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_currentSupport_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_currentSupport_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n))}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ a ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) ≤ ∑ a ∈ finiteBoundaryGhostDecrementedSourceWeightSigmaCurrentSupport n (Ω.image Sigma.fst), finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_currentSupport_sum hβ hH Ω

/--
[finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_cutoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_cutoffSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n))}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ a ∈ Ω, finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a) ≤ finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n (Ω.image Sigma.fst) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_cutoffSum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_selectedPairCutoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_selectedPairCutoffSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ finiteBoundaryGhostSelectedPairCutoffSum β H n Ω := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_selectedPairCutoffSum hβ hH Ω

/--
[finiteBoundaryGhostSelectedPairCutoffSum_le_decrementedSourceWeightCutoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSelectedPairCutoffSum_le_decrementedSourceWeightCutoffSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  finiteBoundaryGhostSelectedPairCutoffSum β H n Ω ≤ finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostSelectedPairCutoffSum_le_decrementedSourceWeightCutoffSum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_decrementedSourceWeightCutoffSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_decrementedSourceWeightCutoffSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_decrementedSourceWeightCutoffSum hβ hH Ω

/--
[finiteBoundaryGhostSigmaTwoPointSourceDataWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaTwoPointSourceDataWeight_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)) :
-- imply
  0 ≤ finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostSigmaTwoPointSourceDataWeight_nonneg hβ hH d

/--
[finiteBoundaryGhostOnePointSourceCutoff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostOnePointSourceCutoff_mem_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ} :
-- imply
  m ∈ finiteBoundaryGhostOnePointSourceCutoff Ω ↔ m ∈ Ω ∧ finiteBoundaryGhostFullSourceOnePoint n m := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostOnePointSourceCutoff_mem Ω m

/--
[finiteBoundaryGhostOnePointSourceCutoff_eq_filter_fullSourceOnePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostOnePointSourceCutoff_eq_filter_fullSourceOnePoint_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostOnePointSourceCutoff Ω = Ω.filter (fun m => finiteBoundaryGhostFullSourceOnePoint n m) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostOnePointSourceCutoff_eq_filter_fullSourceOnePoint Ω

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha_map_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {a : (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).α}
-- given
  (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
-- imply
  (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha Ω hv a) = ⟨v, (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).map a⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_toCollapsedCutoffAlpha_map Ω hv a

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_onePointSourceCutoff_eq_collapsedVertexCutoffDecrementIndex_domain_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_onePointSourceCutoff_eq_collapsedVertexCutoffDecrementIndex_domain_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (finiteBoundaryGhostOnePointSourceCutoff Ω) v = Finset.sum (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).domain (fun a => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).map a)) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_onePointSourceCutoff_eq_collapsedVertexCutoffDecrementIndex_domain_sum Ω v

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_domain_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_domain_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (Ω.filter (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v = Finset.sum (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).domain (fun a => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).map a)) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_domain_sum Ω v

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_domain_sum_eq_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_domain_sum_eq_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  Finset.sum (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).domain (fun a => finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).map a)) = ∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image, (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber d).card : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_domain_sum_eq_image_sum Ω v

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n (Ω.filter (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v = ∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image, (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber d).card : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_image_sum Ω v

/--
[finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  0 ≤ finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight_nonneg hβ hH d

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha_map_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {a : (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).α} :
-- imply
  (finiteBoundaryGhostCutoffDecrementIndex Ω).map (finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha Ω a) = ⟨((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a).1, ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a).2.toSourceData⟩ := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha_map Ω a

/--
[finiteBoundaryGhostSelectedPairCutoffSum_eq_cutoffDecrementIndex_domain_indicator_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSelectedPairCutoffSum_eq_cutoffDecrementIndex_domain_indicator_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostSelectedPairCutoffSum β H n Ω = Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).domain (fun a => (if Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)) = finiteBoundaryGhostOnePointSource 3 n then (1 : ℝ) else 0) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostSelectedPairCutoffSum_eq_cutoffDecrementIndex_domain_indicator_sum Ω

/--
[finiteBoundaryGhostSelectedPairCutoffSum_le_collapsedCutoffDecrementIndex_domain_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSelectedPairCutoffSum_le_collapsedCutoffDecrementIndex_domain_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  finiteBoundaryGhostSelectedPairCutoffSum β H n Ω ≤ Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain (fun a => finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a)) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostSelectedPairCutoffSum_le_collapsedCutoffDecrementIndex_domain_sum hβ hH Ω

/--
[finiteBoundaryGhostCutoffDecrementIndex_mem_domain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_mem_domain_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α} :
-- imply
  a ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).domain := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_mem_domain Ω a

/--
[finiteBoundaryGhostCutoffDecrementIndex_domain_card_eq_crossingPairs_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_domain_card_eq_crossingPairs_sum_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  ((finiteBoundaryGhostCutoffDecrementIndex Ω).domain.card : ℝ) = ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), ∑ m ∈ Ω, ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_domain_card_eq_crossingPairs_sum Ω

/--
[finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_iff_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_iff_map_eq_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)) :
-- imply
  a ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d ↔ (finiteBoundaryGhostCutoffDecrementIndex Ω).map a = d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_iff_map_eq Ω d a

/--
[finiteBoundaryGhostCutoffDecrementIndex_map_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_map_fst_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α} :
-- imply
  ((finiteBoundaryGhostCutoffDecrementIndex Ω).map a).1 = a.1.1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_map_fst Ω a

/--
[finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_fst_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_fst_eq_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)}
  {a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α}
-- given
  (ha : a ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d) :
-- imply
  a.1.1 = d.1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_fst_eq Ω ha

/--
[finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_heq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_heq_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {w : {w : FK.boxVerts 3 n // w ∈ Finset.univ.filter (FK.boxBoundary 3 n)}}
  {m : {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ // m ∈ Ω}}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 w.1}}
-- given
  (ha : (⟨w, ⟨m, p⟩⟩ : (finiteBoundaryGhostCutoffDecrementIndex Ω).α) ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v))) :
-- imply
  HEq (finiteBoundaryGhostBoundaryCrossingPairDecrementData (p := p.1) m.1 w.1 p.2) d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_heq Ω d ha

/--
[finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_eq_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {w : {w : FK.boxVerts 3 n // w ∈ Finset.univ.filter (FK.boxBoundary 3 n)}}
  {m : {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ // m ∈ Ω}}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 w.1}}
-- given
  (ha : (⟨w, ⟨m, p⟩⟩ : (finiteBoundaryGhostCutoffDecrementIndex Ω).α) ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)))
  (hvw : w.1 = v) :
-- imply
  finiteBoundaryGhostBoundaryCrossingPairDecrementData (p := p.1) m.1 w.1 p.2 = (hvw.symm ▸ d) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_eq Ω d ha hvw

/--
[finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_exists_localFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_exists_localFiber_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {w : {w : FK.boxVerts 3 n // w ∈ Finset.univ.filter (FK.boxBoundary 3 n)}}
  {m : {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ // m ∈ Ω}}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 w.1}}
-- given
  (ha : (⟨w, ⟨m, p⟩⟩ : (finiteBoundaryGhostCutoffDecrementIndex Ω).α) ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v))) :
-- imply
  ∃ p' : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 v}, p'.1 = p.1 ∧ p' ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m.1 v d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_exists_localFiber Ω d ha

/--
[finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_val_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {w : {w : FK.boxVerts 3 n // w ∈ Finset.univ.filter (FK.boxBoundary 3 n)}}
  {m : {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ // m ∈ Ω}}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 w.1}}
-- given
  (ha : (⟨w, ⟨m, p⟩⟩ : (finiteBoundaryGhostCutoffDecrementIndex Ω).α) ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v))) :
-- imply
  (finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice Ω d ha).1 = p.1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_val Ω d ha

/--
[finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_mem_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {w : {w : FK.boxVerts 3 n // w ∈ Finset.univ.filter (FK.boxBoundary 3 n)}}
  {m : {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ // m ∈ Ω}}
  {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 w.1}}
-- given
  (ha : (⟨w, ⟨m, p⟩⟩ : (finiteBoundaryGhostCutoffDecrementIndex Ω).α) ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v))) :
-- imply
  finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice Ω d ha ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m.1 v d := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_localFiberChoice_mem Ω d ha

/--
[finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_mem_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v))
  (a : {a // a ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d}) :
-- imply
  finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap Ω d a ∈ Ω.attach.sigma (fun m => (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m.1 d.1 d.2).attach) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_mem Ω d a

/--
[finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_injective_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v} :
-- imply
  Function.Injective (finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap Ω (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v))) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_fiberLocalSigmaMap_injective Ω d

/--
[finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_localFiber_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_localFiber_sum_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v} :
-- imply
  ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v))).card ≤ ∑ m ∈ Ω, (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_localFiber_sum Ω d

/--
[finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)) :
-- imply
  ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card ≤ ∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum Ω d

/--
[finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_eq_zero_of_current_ne_update_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_eq_zero_of_current_ne_update_target_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
-- given
  (hm : m ≠ Function.update d.1 (finiteBoundaryGhostBoundaryEdge n v) (d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1)) :
-- imply
  (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card = 0 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_card_eq_zero_of_current_ne_update_target m v d hm

/--
[finiteBoundaryGhostCutoffDecrementIndex_localFiber_sum_le_decrementedBoundaryGhostMultiplicity_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_localFiber_sum_le_decrementedBoundaryGhostMultiplicity_succ_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v} :
-- imply
  (∑ m ∈ Ω, (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v d).card) ≤ d.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_localFiber_sum_le_decrementedBoundaryGhostMultiplicity_succ Ω d

/--
[finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)) :
-- imply
  ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card ≤ d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ Ω d

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_toSourceData_fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_toSourceData_fiber_card_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤ ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber (⟨d.1, d.2.toSourceData⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v))).card := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_toSourceData_fiber_card Ω d

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤ ∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1) := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_boundaryGhostMultiplicity_sum Ω d

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card ≤ d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostCollapsedCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ Ω d

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_domain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_domain_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {a : (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).α} :
-- imply
  a ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_domain Ω a

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_card_le_crossingPairs_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_card_le_crossingPairs_sum_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain.card : ℝ) ≤ ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), ∑ m ∈ Ω, ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_card_le_crossingPairs_sum Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_image_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_image_iff_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image ↔ ∃ a : (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).α, (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a = d := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_mem_image_iff Ω d

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)}
-- given
  (hd : d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image) :
-- imply
  FK.boxBoundary 3 n d.1 := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_fst_boundary Ω hd

/--
[finiteBoundaryGhostCutoffDecrementIndex_mem_image_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_mem_image_iff_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)) :
-- imply
  d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image ↔ ∃ a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α, (finiteBoundaryGhostCutoffDecrementIndex Ω).map a = d := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_mem_image_iff Ω d

/--
[finiteBoundaryGhostCutoffDecrementIndex_image_fst_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_image_fst_boundary_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)}
-- given
  (hd : d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image) :
-- imply
  FK.boxBoundary 3 n d.1 := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_image_fst_boundary Ω hd

/--
[finiteBoundaryGhostCutoffDecrementIndex_not_mem_image_of_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_not_mem_image_of_not_boundary_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
-- given
  (hv : ¬ FK.boxBoundary 3 n v) :
-- imply
  (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)) ∉ (finiteBoundaryGhostCutoffDecrementIndex Ω).image := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_not_mem_image_of_not_boundary Ω hv d

/--
[finiteBoundaryGhostCutoffDecrementIndex_not_mem_fiber_of_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_not_mem_fiber_of_not_boundary_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
  {a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α}
-- given
  (hv : ¬ FK.boxBoundary 3 n v) :
-- imply
  a ∉ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)) := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_not_mem_fiber_of_not_boundary Ω hv d a

/--
[finiteBoundaryGhostCutoffDecrementIndex_fiber_card_eq_zero_of_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_fiber_card_eq_zero_of_not_boundary_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostTwoPointSourceData n v}
-- given
  (hv : ¬ FK.boxBoundary 3 n v) :
-- imply
  ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v))).card = 0 := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_fiber_card_eq_zero_of_not_boundary Ω hv d

/--
[finiteBoundaryGhostCutoffDecrementIndex_fiber_nonempty_of_mem_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_fiber_nonempty_of_mem_image_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)}
-- given
  (hd : d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image) :
-- imply
  ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).Nonempty := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_fiber_nonempty_of_mem_image Ω hd

/--
[finiteBoundaryGhostCutoffDecrementIndex_fiber_card_pos_of_mem_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_fiber_card_pos_of_mem_image_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostTwoPointSourceData n v)}
-- given
  (hd : d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image) :
-- imply
  0 < ((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_fiber_card_pos_of_mem_image Ω hd

/--
[finiteBoundaryGhostCutoffDecrementIndex_image_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_image_sum_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_image_sum_nonneg hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_nonneg hβ hH Ω

/--
[finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) ≤ ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_weight_sum hβ hH Ω

/--
[finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) ≤ ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum hβ hH Ω

/--
[finiteBoundaryGhostCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_eq_current_weight_sum_add_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_eq_current_weight_sum_add_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).image (fun d => (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d)) = Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).image (fun d => (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d)) + Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).image (fun d => finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_eq_current_weight_sum_add_weight_sum Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_eq_current_weight_sum_add_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_eq_current_weight_sum_add_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) = Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) + Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_eq_current_weight_sum_add_weight_sum Ω

/--
[finiteBoundaryGhostCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_boundary_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_boundary_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).image (fun d => (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d)) = Finset.sum (Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)) (fun v => Finset.sum ((finiteBoundaryGhostCutoffDecrementIndex Ω).image.filter (fun d => d.1 = v)) (fun d => (((d.2.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d))) := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_boundary_sum Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_boundary_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_boundary_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) = Finset.sum (Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)) (fun v => Finset.sum ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image.filter (fun d => d.1 = v)) (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d))) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_boundary_sum Ω

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card_eq
  {n : ℕ}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  (finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d).card = d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card d

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_ends_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d) :
-- imply
  Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i = s(some d.1, none) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_ends d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_mem_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_mem_source_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
-- imply
  i ∈ d.2.toSourceData.2.1 := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_mem_source d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_not_mem_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_not_mem_source_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
-- imply
  i ∉ d.2.toSourceData.2.1 := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_not_mem_source d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_card_le_boundaryMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_card_le_boundaryMultiplicity_eq
  {n : ℕ}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  (finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card ≤ d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_card_le_boundaryMultiplicity d

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_card_le_boundaryMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_card_le_boundaryMultiplicity_eq
  {n : ℕ}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  (finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card ≤ d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_card_le_boundaryMultiplicity d

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_eq_card_mul_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_eq_card_mul_weight_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) = (((finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_eq_card_mul_weight d

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_eq_card_mul_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_eq_card_mul_weight_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) = (((finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_eq_card_mul_weight d

/--
[finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_eq_sq_decrement_weight_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_eq_sq_decrement_weight_of_pos_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hv : FK.boxBoundary 3 n d.1)
  (hpos : 0 < d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1)) :
-- imply
  (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) = (β * H) * (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_eq_sq_decrement_weight_of_pos d hv hpos

/--
[finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_sq_decrement_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_sq_decrement_weight_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hv : FK.boxBoundary 3 n d.1) :
-- imply
  (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ (β * H) * (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_sq_decrement_weight hβ hH d hv

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sq_decrement_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sq_decrement_weight_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hv : FK.boxBoundary 3 n d.1) :
-- imply
  (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ (β * H) * (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sq_decrement_weight hβ hH d hv

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sq_decrement_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sq_decrement_weight_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hv : FK.boxBoundary 3 n d.1) :
-- imply
  (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ (β * H) * (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1))) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sq_decrement_weight hβ hH d hv

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_source_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1))) (copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i d.2.toSourceData.2.1) = finiteBoundaryGhostOnePointSource 3 n := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_source d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_mem_sourceSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_mem_sourceSector_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
-- imply
  copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i d.2.toSourceData.2.1 ∈ finiteBoundaryGhostSourceSector (Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1)) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_mem_sourceSector d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_source_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1))) (copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i d.2.toSourceData.2.1) = (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1}) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_source d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_mem_twoPointSourceSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_mem_twoPointSourceSector_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
-- imply
  copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i d.2.toSourceData.2.1 ∈ finiteBoundaryGhostTwoPointSourceSector (Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1)) d.1 := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_mem_twoPointSourceSector d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_transport_univ_source_onePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_transport_univ_source_onePoint_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d) :
-- imply
  Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1))) (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1)))) = finiteBoundaryGhostOnePointSource 3 n := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_transport_univ_source_onePoint d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_complement_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_complement_source_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
-- imply
  let m' := Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1) let K' := copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i d.2.toSourceData.2.1 Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m') ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m')) \ K') = (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_transport_complement_source d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_complement_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_complement_source_eq
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
-- imply
  let m' := Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1) let K' := copyDeletePreimageDecrementEraseFinset (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1 i d.2.toSourceData.2.1 Sharpness.RandomCurrent.sources (Sharpness.FluxEdgeCopy.endsM (Sharpness.withGhost (FK.boxGraph 3 n)) m') ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m')) \ K') = (∅ : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_transport_complement_source d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_sq_decrement_weight_le_sourcePairSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_sq_decrement_weight_le_sourcePairSummand_eq
  {β H : ℝ}
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d) :
-- imply
  let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let m' := Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1) (β * H) * (β * H) * Sharpness.weight G β J (Sharpness.ofEdgeFun G m') ≤ (β * H) * (β * H) * edgeCopySourcePairSummand G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) m' := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_sq_decrement_weight_le_sourcePairSummand hβ hH d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_sq_decrement_weight_le_sourcePairSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_sq_decrement_weight_le_sourcePairSummand_eq
  {β H : ℝ}
  {n : ℕ}
  {i : Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) d.2.toSourceData.1}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hi : i ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d) :
-- imply
  let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let m' := Function.update d.2.toSourceData.1 i.1 (d.2.toSourceData.1 i.1 - 1) (β * H) * (β * H) * Sharpness.weight G β J (Sharpness.ofEdgeFun G m') ≤ (β * H) * (β * H) * edgeCopySourcePairSummand G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1}) (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) m' := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_sq_decrement_weight_le_sourcePairSummand hβ hH d hi

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sourcePairSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sourcePairSummand_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hv : FK.boxBoundary 3 n d.1) :
-- imply
  let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let m' := Function.update d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1) (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ (β * H) * (β * H) * edgeCopySourcePairSummand G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) m' := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies_weight_sum_le_sourcePairSummand hβ hH d hv

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sourcePairSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sourcePairSummand_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hv : FK.boxBoundary 3 n d.1) :
-- imply
  let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let m' := Function.update d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1) (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ (β * H) * (β * H) * edgeCopySourcePairSummand G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1}) (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) m' := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies_weight_sum_le_sourcePairSummand hβ hH d hv

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card_eq_source_add_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card_eq_source_add_complement_eq
  {n : ℕ}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  (finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d).card = (finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d).card + (finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d).card := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_card_eq_source_add_complement d

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_decrementedBoundaryMultiplicity_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_decrementedBoundaryMultiplicity_weight_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) = (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_decrementedBoundaryMultiplicity_weight d

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_source_add_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_source_add_complement_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v)) :
-- imply
  (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) = (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) + (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_eq_source_add_complement d

/--
[finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_le_sourcePairSum_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_le_sourcePairSum_add_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))
  (hv : FK.boxBoundary 3 n d.1) :
-- imply
  let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) (∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ (β * H) * (β * H) * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) + (β * H) * (β * H) * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1}) (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) := by
-- proof
  apply StatMech.finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies_weight_sum_le_sourcePairSum_add hβ hH d hv

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundaryCopy_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundaryCopy_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) = Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundaryCopy_sum Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sourcePairSum_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sourcePairSum_add_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) ≤ Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (β * H) * (β * H) * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) + (β * H) * (β * H) * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some d.1}) (({some d.1} : Finset (Option (FK.boxVerts 3 n))) ∆ {none})) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sourcePairSum_add hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_sourcePairSum_add_image_sum_eq_regrouped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_sourcePairSum_add_image_sum_eq_regrouped_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let onePoint := C * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) Finset.sum I.image (fun d => onePoint + boundaryPair d.1) = (((I.image.card : ℕ) : ℝ) * onePoint) + ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) * boundaryPair v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_sourcePairSum_add_image_sum_eq_regrouped Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_regrouped_sourcePairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_regrouped_sourcePairSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let onePoint := C * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) Finset.sum I.image (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) ≤ (((I.image.card : ℕ) : ℝ) * onePoint) + ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) * boundaryPair v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_regrouped_sourcePairSum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundarySource_add_complement_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundarySource_add_complement_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) = Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundarySourceCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) + Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => ∑ _ ∈ finiteBoundaryGhostSigmaCollapsedTargetBoundaryComplementCopies d, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_eq_targetBoundarySource_add_complement_sum Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sq_decrement_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sq_decrement_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) ≤ Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (β * H) * (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1)))) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_sq_decrement_weight_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex_sum_fiber_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex_sum_fiber_weight_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (β * H) * (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1)))) = ∑ m' ∈ (finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex Ω).image, (((finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex Ω).fiber m').card : ℝ) * ((β * H) * (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m')) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffSqDecrementCurrentIndex_sum_fiber_weight Ω

/--
[finiteBoundaryGhostCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) = ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) * (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image.filter (fun d => d.1 = v), finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) = ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) * (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image.filter (fun d => d.1 = v), finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_eq_boundary_sum Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryImage_weight_sum_le_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryImage_weight_sum_le_tsum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image.filter (fun d : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v) => d.1 = v), finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ ∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v, finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryImage_weight_sum_le_tsum hβ hH Ω v

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_weight_sum_le_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_weight_sum_le_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_weight_sum_le_emptyCollapsedSum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_tsum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_tsum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) * (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v, finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_tsum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) * ((β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_boundaryMultiplicity_weight_sum_le_emptyCollapsedSum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_tsum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_tsum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) * (∑' d : finiteBoundaryGhostCollapsedTwoPointSourceData n v, finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_tsum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) * ((β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_image_sum_le_boundaryGhostMultiplicity_emptyCollapsedSum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_sum_eq_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_sum_eq_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain (fun a => finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a)) = ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_domain_sum_eq_image_sum Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementIndex_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementIndex_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementIndex_image_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_succ_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_succ_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ d ∈ (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image, (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_succ_weight_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_weight_sum_add_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_weight_sum_add_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (((d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) : ℕ) : ℝ) * finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H d)) + Finset.sum (Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)) (fun v => (β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffDecrementedBoundaryMultiplicity_weight_sum_add_emptyCollapsedSum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_regroupedSourcePairSum_add_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_regroupedSourcePairSum_add_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let onePoint := C * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) let emptyBoundary := fun v : FK.boxVerts 3 n => (β * H) * edgeCopySourcePairEmptyCollapsedSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ((((I.image.card : ℕ) : ℝ) * onePoint) + ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) * boundaryPair v) + ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), emptyBoundary v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_regroupedSourcePairSum_add_emptyCollapsedSum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedCutoffDecrementIndex_regroupedSourcePairSum_eq_boundaryFiberSourcePairSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffDecrementIndex_regroupedSourcePairSum_eq_boundaryFiberSourcePairSum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let onePoint := C * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) let B : Finset (FK.boxVerts 3 n) := Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v) (((I.image.card : ℕ) : ℝ) * onePoint) + ∑ v ∈ B, (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) * boundaryPair v = ∑ v ∈ B, (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) * (onePoint + boundaryPair v) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffDecrementIndex_regroupedSourcePairSum_eq_boundaryFiberSourcePairSum Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairSum_add_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairSum_add_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let onePoint := C * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) let emptyBoundary := fun v : FK.boxVerts 3 n => (β * H) * edgeCopySourcePairEmptyCollapsedSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) let B : Finset (FK.boxVerts 3 n) := Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v) (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ (∑ v ∈ B, (((I.image.filter (fun d => d.1 = v)).card : ℕ) : ℝ) * (onePoint + boundaryPair v)) + ∑ v ∈ B, emptyBoundary v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairSum_add_emptyCollapsedSum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_sq_decrement_weight_sum_add_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_sq_decrement_weight_sum_add_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image (fun d => (β * H) * (β * H) * Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) (Function.update d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) (d.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n d.1) - 1)))) + Finset.sum (Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)) (fun v => (β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_sq_decrement_weight_sum_add_emptyCollapsedSum_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffBoundaryMultiplicity_emptyCollapsedSum_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffBoundaryMultiplicity_emptyCollapsedSum_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) * ((β * H) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffBoundaryMultiplicity_emptyCollapsedSum_sum hβ hH Ω

/--
[finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_domain_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_domain_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω = Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).domain (fun a => finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H ((finiteBoundaryGhostCutoffDecrementIndex Ω).map a)) := by
-- proof
  apply StatMech.finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_domain_sum Ω

/--
[finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω = ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_cutoffDecrementIndex_image_sum Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementIndex_image_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementIndex_image_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d).card : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementIndex_image_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementedBoundaryMultiplicity_succ_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementedBoundaryMultiplicity_succ_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((d.2.1 (finiteBoundaryGhostBoundaryEdge n d.1) + 1 : ℕ) : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffDecrementedBoundaryMultiplicity_succ_weight_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicity_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicity_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image, (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n d.1)) : ℕ) : ℝ) * finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicity_weight_sum hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicity_boundary_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicity_boundary_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), (((∑ m ∈ Ω, m (finiteBoundaryGhostBoundaryEdge n v)) : ℕ) : ℝ) * (∑ d ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).image.filter (fun d => d.1 = v), finiteBoundaryGhostSigmaTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicity_boundary_sum hβ hH Ω

/--
[singleton_symmDiff_card_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma singleton_symmDiff_card_even_eq
  [DecidableEq V]
  {x y : V} :
-- imply
  Even ((({x} : Finset V) ∆ {y}).card) := by
-- proof
  apply StatMech.singleton_symmDiff_card_even x y

/--
[finiteBoundaryGhostOriginalSet_edgeInside_map_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostOriginalSet_edgeInside_map_some_eq
  {d n : ℕ}
  {e : Sym2 (FK.boxVerts d n)} :
-- imply
  Sharpness.edgeInside (finiteBoundaryGhostOriginalSet d n) (Sym2.map some e) := by
-- proof
  apply StatMech.finiteBoundaryGhostOriginalSet_edgeInside_map_some d n e

/--
[finiteBoundaryGhostOriginalSet_not_edgeInside_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostOriginalSet_not_edgeInside_some_none_eq
  {d n : ℕ}
  {x : FK.boxVerts d n} :
-- imply
  ¬ Sharpness.edgeInside (finiteBoundaryGhostOriginalSet d n) s(some x, none) := by
-- proof
  apply StatMech.finiteBoundaryGhostOriginalSet_not_edgeInside_some_none d n x

/--
[finiteBoundaryGhostLocalizedCoupling_map_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedCoupling_map_some_eq
  {d n : ℕ}
  {H : ℝ}
  {e : Sym2 (FK.boxVerts d n)} :
-- imply
  Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet d n) (Sym2.map some e) = 1 := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedCoupling_map_some d n H e

/--
[finiteBoundaryGhostLocalizedCoupling_some_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedCoupling_some_none_eq
  {d n : ℕ}
  {H : ℝ}
  {x : FK.boxVerts d n} :
-- imply
  Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet d n) s(some x, none) = 0 := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedCoupling_some_none d n H x

/--
[finiteBoundaryGhostLocalizedCoupling_pos_of_edgeInside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedCoupling_pos_of_edgeInside_eq
  {d n : ℕ}
  {H : ℝ}
  {e : Sym2 (Option (FK.boxVerts d n))}
-- given
  (he : Sharpness.edgeInside (finiteBoundaryGhostOriginalSet d n) e) :
-- imply
  0 < Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet d n) e := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedCoupling_pos_of_edgeInside d n H he

/--
[finiteBoundaryGhostLocalized_bondSum_eq_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalized_bondSum_eq_original_eq
  {d n : ℕ}
  {H : ℝ}
  {s : ConfigSpace (Option (FK.boxVerts d n))} :
-- imply
  (∑ e ∈ (Sharpness.withGhost (FK.boxGraph d n)).edgeFinset, Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet d n) e * Ising.bond s e) = ∑ e ∈ (FK.boxGraph d n).edgeFinset, (fun _ : Sym2 (FK.boxVerts d n) => (1 : ℝ)) e * Ising.bond (fun x => s (some x)) e := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalized_bondSum_eq_original d n H s

/--
[finiteBoundaryGhostLocalizedCoupling_eq_ghostCoupling_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedCoupling_eq_ghostCoupling_zero_eq
  {d n : ℕ}
  {β H : ℝ} :
-- imply
  Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet d n) = Sharpness.FieldGhostDict.ghostCoupling (0 : ℝ) β (fun _ => 1) := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedCoupling_eq_ghostCoupling_zero d n β H

/--
[finiteBoundaryGhostLocalizedExpectation_symmDiff_eq_boxExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedExpectation_symmDiff_eq_boxExpectation_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) = Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1) (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedExpectation_symmDiff_eq_boxExpectation β H n v

/--
[finiteBoundaryGhostLocalizedExpectation_pair_eq_boxExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedExpectation_pair_eq_boxExpectation_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : IsingFK.boxOrigin 3 n ≠ v) :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) = Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1) (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedExpectation_pair_eq_boxExpectation β H n hv

/--
[boxOrigin_not_boxBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxOrigin_not_boxBoundary_eq
  {d n : ℕ} :
-- imply
  ¬ FK.boxBoundary d n (IsingFK.boxOrigin d n) := by
-- proof
  apply StatMech.boxOrigin_not_boxBoundary d n

/--
[boxOrigin_ne_of_boxBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxOrigin_ne_of_boxBoundary_eq
  {d n : ℕ}
  {v : FK.boxVerts d n}
-- given
  (hv : FK.boxBoundary d n v) :
-- imply
  IsingFK.boxOrigin d n ≠ v := by
-- proof
  apply StatMech.boxOrigin_ne_of_boxBoundary d n hv

/--
[finiteBoundaryGhostLocalizedExpectation_boundary_eq_boxExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedExpectation_boundary_eq_boxExpectation_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : FK.boxBoundary 3 n v) :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) = Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1) (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedExpectation_boundary_eq_boxExpectation β H n hv

/--
[finiteBoundaryGhostLocalizedExpectation_boundary_le_boxExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedExpectation_boundary_le_boxExpectation_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : FK.boxBoundary 3 n v) :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) ≤ Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1) (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedExpectation_boundary_le_boxExpectation β H n hv

/--
[finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hbdry_ne : ∀ v : FK.boxVerts 3 n, FK.boxBoundary 3 n v → IsingFK.boxOrigin 3 n ≠ v) :
-- imply
  (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n)))) = finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum β H n hbdry_ne

/--
[finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum_of_boxGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum_of_boxGeometry_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n)))) = finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedBoundarySum_eq_finiteCurrentBoundaryTwoPointSum_of_boxGeometry β H n

/--
[finiteBoundaryGhostCurrentOnePoint_eq_currentSumRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_eq_currentSumRatio_eq
  {d n : ℕ}
  {β H : ℝ} :
-- imply
  finiteBoundaryGhostCurrentOnePoint d n β H = Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph d n)) β (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource d n) / Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph d n)) β (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_eq_currentSumRatio d n β H

/--
[finiteBoundaryGhostCurrentOnePoint_eq_expectationJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_eq_expectationJ_eq
  {d n : ℕ}
  {β H : ℝ} :
-- imply
  finiteBoundaryGhostCurrentOnePoint d n β H = Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph d n)) β (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource d n) := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_eq_expectationJ d n β H

/--
[finiteBoundaryGhostCurrentOnePoint_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_nonneg_eq
  {d n : ℕ}
  {β H : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostCurrentOnePoint d n β H := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_nonneg d n hβ hH

/--
[finiteBoundaryGhostCurrentOnePoint_eq_expectationJ_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_eq_expectationJ_pair_eq
  {d n : ℕ}
  {β H : ℝ} :
-- imply
  finiteBoundaryGhostCurrentOnePoint d n β H = Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph d n)) β (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) ({some (IsingFK.boxOrigin d n), none} : Finset (Option (FK.boxVerts d n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_eq_expectationJ_pair d n β H

/--
[spinProd_some_none_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma spinProd_some_none_split_eq
  [DecidableEq V]
  {o : V}
  {b : Bool}
  {τ : ConfigSpace V} :
-- imply
  Ising.spinProd ({some o, none} : Finset (Option V)) (fun a => Option.rec b τ a) = Ising.spin τ o * Ising.spinB b := by
-- proof
  apply StatMech.spinProd_some_none_split o b τ

/--
[ghostCoupling_zero_some_none_numerator_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma ghostCoupling_zero_some_none_numerator_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  (∑ s : ConfigSpace (Option V), Ising.spinProd ({some o, none} : Finset (Option V)) s * Sharpness.boltzmannJ (Sharpness.withGhost G) β (Sharpness.FieldGhostDict.ghostCoupling (0 : ℝ) β (fun _ => 1)) s) = 0 := by
-- proof
  apply StatMech.ghostCoupling_zero_some_none_numerator_eq_zero G β o

/--
[expectationJ_ghostCoupling_zero_some_none_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma expectationJ_ghostCoupling_zero_some_none_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost G) β (Sharpness.FieldGhostDict.ghostCoupling (0 : ℝ) β (fun _ => 1)) ({some o, none} : Finset (Option V)) = 0 := by
-- proof
  apply StatMech.expectationJ_ghostCoupling_zero_some_none_eq_zero G β o

/--
[finiteBoundaryGhostExpectation_zeroField_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostExpectation_zeroField_eq_zero_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) = 0 := by
-- proof
  apply StatMech.finiteBoundaryGhostExpectation_zeroField_eq_zero β n

/--
[finiteBoundaryGhostSimonWeight_some_none_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonWeight_some_none_of_boundary_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : FK.boxBoundary 3 n v) :
-- imply
  finiteBoundaryGhostSimonWeight β H n (some v) none = Real.tanh (β * H) * Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonWeight_some_none_of_boundary β H n hv

/--
[finiteBoundaryGhostSimonWeight_some_none_of_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonWeight_some_none_of_not_boundary_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : ¬ FK.boxBoundary 3 n v) :
-- imply
  finiteBoundaryGhostSimonWeight β H n (some v) none = 0 := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonWeight_some_none_of_not_boundary β H n hv

/--
[finiteBoundaryGhostSimonWeight_sum_originalSet_eq_boundarySum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonWeight_sum_originalSet_eq_boundarySum_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) = ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), finiteBoundaryGhostSimonWeight β H n (some v) none := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonWeight_sum_originalSet_eq_boundarySum β H n

/--
[finiteBoundaryGhostSimonWeight_boundarySum_eq_tanh_mul_localizedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonWeight_boundarySum_eq_tanh_mul_localizedSum_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), finiteBoundaryGhostSimonWeight β H n (some v) none) = Real.tanh (β * H) * ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonWeight_boundarySum_eq_tanh_mul_localizedSum β H n

/--
[finiteBoundaryGhostSimonWeight_sum_zeroField_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonWeight_sum_zeroField_eq_zero_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β (0 : ℝ) n x none) = 0 := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonWeight_sum_zeroField_eq_zero β n

/--
[finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum_of_localization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum_of_localization_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hloc : ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) → Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) ≤ Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1) (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v})) :
-- imply
  (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) ≤ finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum_of_localization hβ hH hloc

/--
[finiteBoundaryGhostCurrentOnePoint_le_simonWeightSum_of_singletonSimonLieb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_le_simonWeightSum_of_singletonSimonLieb_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hSL : Sharpness.SimonLieb (fun a b : Option (FK.boxVerts 3 n) => Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b})) (some (IsingFK.boxOrigin 3 n)) (finiteBoundaryGhostOriginalSet 3 n) (finiteBoundaryGhostSimonWeight β H n) ({none} : Finset (Option (FK.boxVerts 3 n)))) :
-- imply
  finiteBoundaryGhostCurrentOnePoint 3 n β H ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_le_simonWeightSum_of_singletonSimonLieb hSL

/--
[finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hSL : Sharpness.SimonLieb (fun a b : Option (FK.boxVerts 3 n) => Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b})) (some (IsingFK.boxOrigin 3 n)) (finiteBoundaryGhostOriginalSet 3 n) (finiteBoundaryGhostSimonWeight β H n) ({none} : Finset (Option (FK.boxVerts 3 n))))
  (hsum : (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) ≤ finiteCurrentBoundaryTwoPointSum β n) :
-- imply
  finiteBoundaryGhostCurrentOnePoint 3 n β H ≤ finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb hSL hsum

/--
[finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLiebLocalization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLiebLocalization_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hSL : Sharpness.SimonLieb (fun a b : Option (FK.boxVerts 3 n) => Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b})) (some (IsingFK.boxOrigin 3 n)) (finiteBoundaryGhostOriginalSet 3 n) (finiteBoundaryGhostSimonWeight β H n) ({none} : Finset (Option (FK.boxVerts 3 n))))
  (hloc : ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) → Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) ≤ Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1) (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v})) :
-- imply
  finiteBoundaryGhostCurrentOnePoint 3 n β H ≤ finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLiebLocalization hβ hH hSL hloc

/--
[finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) ≤ finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonWeight_sum_le_currentBoundaryTwoPointSum hβ hH

/--
[finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb'_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hSL : Sharpness.SimonLieb (fun a b : Option (FK.boxVerts 3 n) => Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b})) (some (IsingFK.boxOrigin 3 n)) (finiteBoundaryGhostOriginalSet 3 n) (finiteBoundaryGhostSimonWeight β H n) ({none} : Finset (Option (FK.boxVerts 3 n)))) :
-- imply
  finiteBoundaryGhostCurrentOnePoint 3 n β H ≤ finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb' hβ hH hSL

/--
[finiteBoundaryGhostSingletonSimonLieb_of_scalarBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSingletonSimonLieb_of_scalarBound_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hbound : Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) :
-- imply
  Sharpness.SimonLieb (fun a b : Option (FK.boxVerts 3 n) => Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({a} : Finset (Option (FK.boxVerts 3 n))) ∆ {b})) (some (IsingFK.boxOrigin 3 n)) (finiteBoundaryGhostOriginalSet 3 n) (finiteBoundaryGhostSimonWeight β H n) ({none} : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostSingletonSimonLieb_of_scalarBound hβ hH hbound

/--
[finiteBoundaryGhostApprox_pointwise_of_hardFieldLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostApprox_pointwise_of_hardFieldLimit_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hlim : Tendsto (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint 3 n β H) atTop (𝓝 (IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β (IsingFK.boxOrigin 3 n)))) :
-- imply
  ∀ ε : ℝ, 0 < ε → ∃ H : ℝ, 0 ≤ H ∧ IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β (IsingFK.boxOrigin 3 n) ≤ finiteBoundaryGhostCurrentOnePoint 3 n β H + ε := by
-- proof
  apply StatMech.finiteBoundaryGhostApprox_pointwise_of_hardFieldLimit hlim

/--
[finiteBoundaryGhostApprox_of_hardFieldLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostApprox_of_hardFieldLimit_eq
-- given
  (hlim : FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical := by
-- proof
  apply StatMech.finiteBoundaryGhostApprox_of_hardFieldLimit hlim

/--
[finiteBoundaryGhostScalarBound_of_currentOnePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostScalarBound_of_currentOnePoint_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hcurrent : finiteBoundaryGhostCurrentOnePoint 3 n β H ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none := by
-- proof
  apply StatMech.finiteBoundaryGhostScalarBound_of_currentOnePoint hcurrent

/--
[finiteBoundaryGhostCurrentOnePoint_le_simonWeightSum_of_scalarBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_le_simonWeightSum_of_scalarBound_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hbound : Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) :
-- imply
  finiteBoundaryGhostCurrentOnePoint 3 n β H ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_le_simonWeightSum_of_scalarBound hbound

/--
[finiteBoundaryGhostCurrentOnePoint_le_of_currentSumBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_le_of_currentSumBound_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hbound : Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) ∅) :
-- imply
  finiteBoundaryGhostCurrentOnePoint 3 n β H ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_le_of_currentSumBound hbound

/--
[finiteBoundaryGhostScalarBound_of_currentSumBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostScalarBound_of_currentSumBound_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hbound : Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) ∅) :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none := by
-- proof
  apply StatMech.finiteBoundaryGhostScalarBound_of_currentSumBound hbound

/--
[finiteBoundaryGhostCurrentSumBound_of_sourcePairBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentSumBound_of_sourcePairBound_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hpair : Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))) (∅ : Finset (Option (FK.boxVerts 3 n)))) :
-- imply
  Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) ∅ := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentSumBound_of_sourcePairBound hpair

/--
[finiteBoundaryGhostSourcePairBound_of_edgeCopyBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSourcePairBound_of_edgeCopyBound_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hcopy : edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))) (∅ : Finset (Option (FK.boxVerts 3 n)))) :
-- imply
  Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * Sharpness.sourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))) (∅ : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostSourcePairBound_of_edgeCopyBound hcopy

/--
[finiteBoundaryGhostEdgeCopyBound_of_emptyCollapsedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostEdgeCopyBound_of_emptyCollapsedBound_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hcopy : edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n)))) :
-- imply
  edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))) (∅ : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostEdgeCopyBound_of_emptyCollapsedBound hcopy

/--
[finiteBoundaryGhostScalarBound_of_emptyCollapsedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostScalarBound_of_emptyCollapsedBound_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hcopy : edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n)))) :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none := by
-- proof
  apply StatMech.finiteBoundaryGhostScalarBound_of_emptyCollapsedBound hcopy

/--
[finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_emptyCollapsedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_emptyCollapsedBound_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hcopy : edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β H n x none) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n)))) :
-- imply
  finiteBoundaryGhostCurrentOnePoint 3 n β H ≤ finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_emptyCollapsedBound hβ hH hcopy

/--
[finiteBoundaryGhostEdgeCopySourcePairSum_zeroField_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostEdgeCopySourcePairSum_zeroField_eq_zero_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  edgeCopySourcePairSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) = 0 := by
-- proof
  apply StatMech.finiteBoundaryGhostEdgeCopySourcePairSum_zeroField_eq_zero β n

/--
[finiteBoundaryGhostCollapsedEdgeCopySum_zeroField_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedEdgeCopySum_zeroField_eq_zero_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) = 0 := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedEdgeCopySum_zeroField_eq_zero β n

/--
[finiteBoundaryGhostCollapsedEdgeCopyBound_zeroField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedEdgeCopyBound_zeroField_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1)) (finiteBoundaryGhostOnePointSource 3 n) ≤ (∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β (0 : ℝ) n x none) * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedEdgeCopyBound_zeroField β n

/--
[real_tanh_pos_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma real_tanh_pos_of_pos_eq
  {x : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  0 < Real.tanh x := by
-- proof
  apply StatMech.real_tanh_pos_of_pos hx

/--
[finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_nonneg hβ hH v

/--
[finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_simonWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_simonWeight_pos_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hweight : 0 < finiteBoundaryGhostSimonWeight β H n (some v) none) :
-- imply
  0 < finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_simonWeight_pos v hweight

/--
[finiteBoundaryGhostLocalizedBoundaryExpectation_pos_of_positive_edgeCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedBoundaryExpectation_pos_of_positive_edgeCurrent_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hsrc : Sharpness.sources (Sharpness.withGhost (FK.boxGraph 3 n)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) = ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))))
  (hweight : 0 < Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
-- imply
  0 < Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedBoundaryExpectation_pos_of_positive_edgeCurrent hβ hH v m hsrc hweight

/--
[finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_boundary_current_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_boundary_current_witness_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hβ : 0 < β)
  (hH : 0 < H)
  (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
  (hsrc : Sharpness.sources (Sharpness.withGhost (FK.boxGraph 3 n)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) = ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))))
  (hweight : 0 < Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
-- imply
  0 < finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_pos_of_boundary_current_witness hβ hH v hv m hsrc hweight

/--
[finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n = ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct β H n

/--
[finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_tanh_mul_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_tanh_mul_normalized_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n = Real.tanh (β * H) * finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n := by
-- proof
  apply StatMech.finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_tanh_mul_normalized β H n

/--
[finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_finiteCurrentBoundaryTwoPointSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_finiteCurrentBoundaryTwoPointSum_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  finiteBoundaryGhostLocalizedBoundaryExpectationSum β H n = finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_finiteCurrentBoundaryTwoPointSum β H n

/--
[finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_currentSumRatio_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_currentSumRatio_sum_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  finiteBoundaryGhostLocalizedBoundaryExpectationSum β H n = ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) / Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) (∅ : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostLocalizedBoundaryExpectationSum_eq_currentSumRatio_sum β H n

/--
[finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_emptyCollapsedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_emptyCollapsedSum_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n = finiteCurrentBoundaryTwoPointSum β n * edgeCopySourcePairEmptyCollapsedSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))) := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_emptyCollapsedSum β H n

/--
[finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_currentSum_empty_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_currentSum_empty_sq_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n = finiteCurrentBoundaryTwoPointSum β n * (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))) * Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n)))) := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_currentSum_empty_sq β H n

/--
[finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_currentSumRatio_sum_mul_currentSum_empty_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_currentSumRatio_sum_mul_currentSum_empty_sq_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n = (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) ({some (IsingFK.boxOrigin 3 n), some v} : Finset (Option (FK.boxVerts 3 n))) / Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (Sharpness.couplingIn (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (finiteBoundaryGhostOriginalSet 3 n)) (∅ : Finset (Option (FK.boxVerts 3 n)))) * (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n))) * Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (∅ : Finset (Option (FK.boxVerts 3 n)))) := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_currentSumRatio_sum_mul_currentSum_empty_sq β H n

/--
[finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile_eq_tanh_mul_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile_eq_tanh_mul_normalized_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hT : Real.tanh (β * H) ≠ 0) :
-- imply
  finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile β H n Ω = Real.tanh (β * H) * finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile_eq_tanh_mul_normalized Ω hT

/--
[finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile_eq_currentProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile_eq_currentProfile_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile β H n Ω = finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCurrentProfile β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile_eq_currentProfile β H n Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicityCollapsedProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicityCollapsedProfile_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicityCollapsedProfile hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_tanh_mul_normalizedCutoffBoundaryMultiplicityCollapsedProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_tanh_mul_normalizedCutoffBoundaryMultiplicityCollapsedProfile_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hT : Real.tanh (β * H) ≠ 0) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ Real.tanh (β * H) * finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_tanh_mul_normalizedCutoffBoundaryMultiplicityCollapsedProfile hβ hH Ω hT

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorption_of_boundaryVertexDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorption_of_boundaryVertexDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorption_of_boundaryVertexDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorption_of_sigmaFiniteSubcaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorption_of_sigmaFiniteSubcaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorption_of_sigmaFiniteSubcaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorption_of_finiteDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorption_of_finiteDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorption_of_finiteDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorption_of_sigmaDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorption_of_sigmaDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorption_of_sigmaDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_globalDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_globalDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_globalDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_decrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_decrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_decrementedSourceAbsorption h

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_nonneg_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  0 ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_nonneg Ω v

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_collapsedCutoff_fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_collapsedCutoff_fiber_card_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostCollapsedTwoPointSourceData n v}
-- given
  (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
-- imply
  ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber d).card ≤ ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).fiber (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n => finiteBoundaryGhostCollapsedTwoPointSourceData n v))).card := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_collapsedCutoff_fiber_card Ω hv d

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostCollapsedTwoPointSourceData n v}
-- given
  (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
-- imply
  ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber d).card ≤ d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ Ω hv d

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
-- imply
  (∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image, (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber d).card : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤ ∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image, (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum hβ hH Ω hv

/--
[finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_localFiber_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_localFiber_sum_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v} :
-- imply
  ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).fiber D).card ≤ ∑ m ∈ Ω, (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber m v D.2.toSourceData).card := by
-- proof
  apply StatMech.finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_localFiber_sum Ω D

/--
[finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
  {D : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v} :
-- imply
  ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).fiber D).card ≤ D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 := by
-- proof
  apply StatMech.finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_fiber_card_le_decrementedBoundaryGhostMultiplicity_succ Ω D

/--
[finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ D ∈ (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).image, (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).fiber D).card : ℝ) * finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D) ≤ ∑ D ∈ (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).image, (((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ) * finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D) := by
-- proof
  apply StatMech.finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum hβ hH Ω v

/--
[finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_fullSourceClassifiedVertexCurrentSupportDecrementedBoundaryGhostMultiplicity_succ_weight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_fullSourceClassifiedVertexCurrentSupportDecrementedBoundaryGhostMultiplicity_succ_weight_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v ≤ ∑ D ∈ (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex Ω v).image, (((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ) * finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H D) := by
-- proof
  apply StatMech.finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_fullSourceClassifiedVertexCurrentSupportDecrementedBoundaryGhostMultiplicity_succ_weight_sum hβ hH Ω v

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_le_boundaryFiberCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_le_boundaryFiberCard_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
-- imply
  ((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image.card : ℝ) ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_le_boundaryFiberCard Ω hv

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_image_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_image_card_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤ ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).image.card : ℝ) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_image_card Ω v

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_domain_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_domain_card_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤ ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain.card : ℝ) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_domain_card Ω v

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_nonneg_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  0 ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_nonneg Ω

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairs_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairs_sum_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤ ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n), ∑ m ∈ Ω, ((finiteBoundaryGhostBoundaryCrossingPairs m w).card : ℝ) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairs_sum Ω v

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairCap_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairCap Ω v

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberDecrementImageMultiplicityCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberDecrementImageMultiplicityCap_nonneg_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  0 ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberDecrementImageMultiplicityCap n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberDecrementImageMultiplicityCap_nonneg Ω

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_decrementImageMultiplicityCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_decrementImageMultiplicityCap_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberDecrementImageMultiplicityCap n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_decrementImageMultiplicityCap Ω

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_nonneg_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  0 ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_nonneg Ω

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_sourceSectorMultiplicityCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_sourceSectorMultiplicityCap_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_sourceSectorMultiplicityCap Ω

/--
[finiteBoundaryGhostBoundaryGhostMultiplicitySum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryGhostMultiplicitySum_nonneg_eq
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ} :
-- imply
  0 ≤ finiteBoundaryGhostBoundaryGhostMultiplicitySum n m := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryGhostMultiplicitySum_nonneg m

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_eq_sourceSectorBoundaryGhostMultiplicityCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_eq_sourceSectorBoundaryGhostMultiplicityCap_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap n Ω = finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorBoundaryGhostMultiplicityCap n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_eq_sourceSectorBoundaryGhostMultiplicityCap Ω

/--
[finiteBoundaryGhostSourceSector_card_le_boundaryCrossingPairCount_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostSourceSector_card_le_boundaryCrossingPairCount_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
-- given
  (hweight : Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
-- imply
  ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤ ∑ w ∈ Finset.univ.filter (fun w : FK.boxVerts 3 n => FK.boxBoundary 3 n w), (finiteBoundaryGhostBoundaryCrossingPairCount m w : ℝ) := by
-- proof
  apply StatMech.finiteBoundaryGhostSourceSector_card_le_boundaryCrossingPairCount_sum m hweight

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  0 ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg Ω

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hΩweight : ∀ m, m ∈ Ω → Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)) (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
-- imply
  finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap n Ω ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap Ω hΩweight

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap_weightNonzeroCutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap_weightNonzeroCutoff_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap_weightNonzeroCutoff Ω

/--
[finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_sum_eq_image_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_sum_eq_image_card_eq
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let B : Finset (FK.boxVerts 3 n) := Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v) (I.image.card : ℝ) = ∑ v ∈ B, finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_sum_eq_image_card Ω

/--
[finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_eq_onePoint_add_boundaryPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_eq_onePoint_add_boundaryPair_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v = finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n + finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_eq_onePoint_add_boundaryPair β H n v

/--
[finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg hβ hH

/--
[finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg hβ hH v

/--
[finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n} :
-- imply
  finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v = finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v * finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v + finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty β H n Ω v

/--
[finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_nonneg hβ hH v

/--
[finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_nonneg hβ hH v

/--
[finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposed_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let onePoint := C * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) let emptyBoundary := fun v : FK.boxVerts 3 n => (β * H) * edgeCopySourcePairEmptyCollapsedSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) let B : Finset (FK.boxVerts 3 n) := Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v) finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω = (I.image.card : ℝ) * onePoint + (∑ v ∈ B, finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v * boundaryPair v) + ∑ v ∈ B, emptyBoundary v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposed β H Ω

/--
[finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposedSourcePairBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposedSourcePairBound_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω = finiteBoundaryGhostBoundaryFiberDecomposedSourcePairBound β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairProfile_eq_decomposedSourcePairBound β H n Ω

/--
[finiteBoundaryGhostBoundaryFiberBoundaryPairWeighted_sum_le_image_card_mul_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberBoundaryPairWeighted_sum_le_image_card_mul_sum_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) let B : Finset (FK.boxVerts 3 n) := Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v) (∑ v ∈ B, finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v * boundaryPair v) ≤ (I.image.card : ℝ) * ∑ v ∈ B, boundaryPair v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberBoundaryPairWeighted_sum_le_image_card_mul_sum hβ hH Ω

/--
[finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_image_card_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_image_card_bound_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let onePoint := C * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) let emptyBoundary := fun v : FK.boxVerts 3 n => (β * H) * edgeCopySourcePairEmptyCollapsedSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) let B : Finset (FK.boxVerts 3 n) := Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v) finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤ (I.image.card : ℝ) * (onePoint + ∑ v ∈ B, boundaryPair v) + ∑ v ∈ B, emptyBoundary v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_image_card_bound hβ hH Ω

/--
[finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound_eq_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound_eq_components_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound β H n Ω = finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent β H n Ω + finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent β H n Ω + finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound_eq_components β H n Ω

/--
[finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 < β)
  (hH : 0 < H) :
-- imply
  0 ≤ finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent_nonneg hβ hH Ω

/--
[finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 < β)
  (hH : 0 < H) :
-- imply
  0 ≤ finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent_nonneg hβ hH Ω

/--
[finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 < β)
  (hH : 0 < H) :
-- imply
  0 ≤ finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent_nonneg hβ hH Ω

/--
[finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_boundaryFiberImageCardCurrentDenominator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_boundaryFiberImageCardCurrentDenominator_eq
  {β H : ℝ}
  {n : ℕ} :
-- imply
  finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n = finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator β H n := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_boundaryFiberImageCardCurrentDenominator β H n

/--
[finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator β H n := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator_nonneg hβ hH

/--
[finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound_eq_tanh_mul_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound_eq_tanh_mul_normalized_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hT : Real.tanh (β * H) ≠ 0) :
-- imply
  finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω = Real.tanh (β * H) * finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound_eq_tanh_mul_normalized Ω hT

/--
[finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound_eq_currentBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound_eq_currentBound_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)} :
-- imply
  finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound β H n Ω = finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound_eq_currentBound β H n Ω

/--
[finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound_nonneg hβ hH Ω

/--
[finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_imageCardSourcePairBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_imageCardSourcePairBound_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤ finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_imageCardSourcePairBound hβ hH Ω

/--
[finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_imageCardSourcePairBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_imageCardSourcePairBound_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hbound : finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω ≤ finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n) :
-- imply
  finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤ finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_imageCardSourcePairBound hβ hH Ω hbound

/--
[finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_decomposed_le_boundaryVertexProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_decomposed_le_boundaryVertexProduct_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hdecomposed : let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let onePoint := C * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) let emptyBoundary := fun v : FK.boxVerts 3 n => (β * H) * edgeCopySourcePairEmptyCollapsedSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) let B : Finset (FK.boxVerts 3 n) := Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v) (I.image.card : ℝ) * onePoint + (∑ v ∈ B, finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v * boundaryPair v) + ∑ v ∈ B, emptyBoundary v ≤ ∑ v ∈ B, finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v) :
-- imply
  finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤ finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_decomposed_le_boundaryVertexProduct β H Ω hdecomposed

/--
[finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_decomposedSourcePairBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_decomposedSourcePairBound_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hbound : finiteBoundaryGhostBoundaryFiberDecomposedSourcePairBound β H n Ω ≤ ∑ v ∈ Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v), finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v) :
-- imply
  finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤ finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_decomposedSourcePairBound β H Ω hbound

/--
[finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_imageCardBound_le_boundaryVertexProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_imageCardBound_le_boundaryVertexProduct_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hbound : let I := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω let G := Sharpness.withGhost (FK.boxGraph 3 n) let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1) let C := (β * H) * (β * H) let onePoint := C * edgeCopySourcePairSum G β J (finiteBoundaryGhostOnePointSource 3 n) (∅ : Finset (Option (FK.boxVerts 3 n))) let boundaryPair := fun v : FK.boxVerts 3 n => C * edgeCopySourcePairSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) (({some v} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) let emptyBoundary := fun v : FK.boxVerts 3 n => (β * H) * edgeCopySourcePairEmptyCollapsedSum G β J (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) let B : Finset (FK.boxVerts 3 n) := Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v) (I.image.card : ℝ) * (onePoint + ∑ v ∈ B, boundaryPair v) + ∑ v ∈ B, emptyBoundary v ≤ ∑ v ∈ B, finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v) :
-- imply
  finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤ finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_imageCardBound_le_boundaryVertexProduct hβ hH Ω hbound

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile hβ hH Ω

/--
[finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile_weightNonzeroCutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile_weightNonzeroCutoff_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤ finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile_weightNonzeroCutoff hβ hH Ω

/--
[finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_nonneg hβ hH Ω v

/--
[finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_le_of_boundaryFiberCard_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_le_of_boundaryFiberCard_le_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω Ω' : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hcard : finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v ≤ finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω' v) :
-- imply
  finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω' v := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_le_of_boundaryFiberCard_le hβ hH hcard

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_mul_main_add_empty_le_boundaryFiberSourcePairVertexProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_mul_main_add_empty_le_boundaryFiberSourcePairVertexProfile_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
-- imply
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v ((I.image.card : ℝ) * finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v + finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v) ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_mul_main_add_empty_le_boundaryFiberSourcePairVertexProfile hβ hH Ω hv

/--
[finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_boundaryFiberSourcePairVertexMainTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_boundaryFiberSourcePairVertexMainTerm_eq
  {β H : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {d : finiteBoundaryGhostCollapsedTwoPointSourceData n v}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hv : FK.boxBoundary 3 n v) :
-- imply
  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_boundaryFiberSourcePairVertexMainTerm hβ hH hv d

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_image_card_mul_main](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_image_card_mul_main_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
-- imply
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v (∑ d ∈ I.image, (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤ (I.image.card : ℝ) * finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_weight_sum_le_image_card_mul_main hβ hH Ω hv

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_weight_sum_le_boundaryFiberSourcePairVertexEmptyTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_weight_sum_le_boundaryFiberSourcePairVertexEmptyTerm_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v (∑ d ∈ I.image, finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_weight_sum_le_boundaryFiberSourcePairVertexEmptyTerm hβ hH Ω v

/--
[finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_le_image_card_mul_main_add_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_le_image_card_mul_main_add_empty_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
  {v : FK.boxVerts 3 n}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H)
  (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
-- imply
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v (∑ d ∈ I.image, (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ) * finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤ (I.image.card : ℝ) * finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v + finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
-- proof
  apply StatMech.finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_le_image_card_mul_main_add_empty hβ hH Ω hv

/--
[finiteBoundaryGhostBoundaryFiberSourcePairProfile_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostBoundaryFiberSourcePairProfile_nonneg_eq
  {β H : ℝ}
  {n : ℕ}
  {Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
-- given
  (hβ : 0 ≤ β)
  (hH : 0 ≤ H) :
-- imply
  0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω := by
-- proof
  apply StatMech.finiteBoundaryGhostBoundaryFiberSourcePairProfile_nonneg hβ hH Ω

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorption_of_componentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorption_of_componentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorption_of_componentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorption_of_currentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorption_of_currentSumAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorption_of_currentSumAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorption_of_currentAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorption_of_currentAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorption_of_currentAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorption_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorption_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorption_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberImageCardSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberImageCardSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberImageCardSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberDecomposedSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberDecomposedSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecomposedSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberDecomposedSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairProfileAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairProfileAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairProfileAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberImageCardSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberImageCardSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberImageCardSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecomposedSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecomposedSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecomposedSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecomposedSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitness_of_originalPathWitness3D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitness_of_originalPathWitness3D_eq
-- given
  (hpath : FiniteBoundaryGhostOriginalPathWitness3D) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitness_of_originalPathWitness3D hpath

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitness_of_boundaryVertexDenominatorPositiveSupportCurrentWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitness_of_boundaryVertexDenominatorPositiveSupportCurrentWitness_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitness_of_boundaryVertexDenominatorPositiveSupportCurrentWitness h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveCurrentWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveCurrentWitness_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveCurrentWitness h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveSupportCurrentWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveSupportCurrentWitness_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveSupportCurrentWitness h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_originalPathWitness3D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_originalPathWitness3D_eq
-- given
  (hpath : FiniteBoundaryGhostOriginalPathWitness3D) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_originalPathWitness3D hpath

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSumAbsorption_eq
-- given
  (hpos : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical)
  (hsum : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSumAbsorption hpos hsum

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveCurrentWitness_componentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveCurrentWitness_componentSumAbsorption_eq
-- given
  (hpos : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical)
  (hsum : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveCurrentWitness_componentSumAbsorption hpos hsum

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveSupportCurrentWitness_componentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveSupportCurrentWitness_componentSumAbsorption_eq
-- given
  (hpos : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical)
  (hsum : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveSupportCurrentWitness_componentSumAbsorption hpos hsum

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_originalPathWitness3D_componentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_originalPathWitness3D_componentSumAbsorption_eq
-- given
  (hpath : FiniteBoundaryGhostOriginalPathWitness3D)
  (hsum : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_originalPathWitness3D_componentSumAbsorption hpath hsum

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberUniformCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberUniformCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberUniformCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberUniformCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberUniformCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberUniformCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryVertexDenominatorPositive_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryVertexDenominatorPositive_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorption_eq
-- given
  (hpos : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical)
  (hsum : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryVertexDenominatorPositive_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorption hpos hsum

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryVertexDenominatorPositiveCurrentWitness_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryVertexDenominatorPositiveCurrentWitness_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorption_eq
-- given
  (hpos : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical)
  (hsum : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryVertexDenominatorPositiveCurrentWitness_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorption hpos hsum

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedAbsorption_of_currentAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedAbsorption_of_currentAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedCurrentAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedAbsorption_of_currentAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorption_of_tanhNormalizedAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorption_of_tanhNormalizedAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorption_of_tanhNormalizedAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryMultiplicityAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryMultiplicityAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryMultiplicityAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteSubcaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteSubcaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteSubcaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteLabelCaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteLabelCaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteLabelCaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_globalDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_globalDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_globalDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaFiniteSubcaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaFiniteSubcaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaFiniteSubcaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryMultiplicityAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryMultiplicityAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryMultiplicityAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairProfileAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairProfileAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairProfileAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberImageCardSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberImageCardSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberImageCardSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecomposedSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecomposedSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecomposedSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecomposedSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteBoundaryGhostScalarBound_zeroField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteBoundaryGhostScalarBound_zeroField_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β (0 : ℝ) n x none := by
-- proof
  apply StatMech.finiteBoundaryGhostScalarBound_zeroField β n

/--
[finiteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical_H0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical_H0_eq :
-- imply
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1)) (({some (IsingFK.boxOrigin 3 n)} : Finset (Option (FK.boxVerts 3 n))) ∆ {none}) ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n, finiteBoundaryGhostSimonWeight β (0 : ℝ) n x none := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical_H0

/--
[finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBound_of_firstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBound_of_firstExitPositive_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBound_of_firstExitPositive h

/--
[finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCurrentBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentBound h

/--
[finiteQ2SimonBoundaryGhostScalarCurrentBound_of_scalarCurrentSumBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCurrentBound_of_scalarCurrentSumBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCurrentSumBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCurrentBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCurrentBound_of_scalarCurrentSumBound h

/--
[finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentSumBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentSumBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCurrentSumBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentSumBound h

/--
[finiteQ2SimonBoundaryGhostScalarCurrentSumBound_of_sourcePairBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarCurrentSumBound_of_sourcePairBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCurrentSumBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarCurrentSumBound_of_sourcePairBound h

/--
[finiteQ2SimonBoundaryGhostScalarBound_of_sourcePairBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarBound_of_sourcePairBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarBound_of_sourcePairBound h

/--
[finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_edgeCopyBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_edgeCopyBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_edgeCopyBound h

/--
[finiteQ2SimonBoundaryGhostScalarBound_of_edgeCopyBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarBound_of_edgeCopyBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarBound_of_edgeCopyBound h

/--
[finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_emptyCollapsedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_emptyCollapsedBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_emptyCollapsedBound h

/--
[finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_emptyCollapsedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_emptyCollapsedBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_emptyCollapsedBound h

/--
[finiteQ2SimonBoundaryGhostScalarBound_of_emptyCollapsedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarBound_of_emptyCollapsedBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarBound_of_emptyCollapsedBound h

/--
[finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_firstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_firstExitPositive_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_firstExitPositive h

/--
[finiteQ2SimonBoundaryGhostScalarBound_of_firstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostScalarBound_of_firstExitPositive_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostScalarBound_of_firstExitPositive h

/--
[finiteQ2SimonBoundaryGhostSingletonSimonLieb_of_scalarBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostSingletonSimonLieb_of_scalarBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostSingletonSimonLiebPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostSingletonSimonLieb_of_scalarBound h

/--
[finiteQ2SimonBoundaryGhostSingletonSimonLiebLocalization_of_singletonSimonLieb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostSingletonSimonLiebLocalization_of_singletonSimonLieb_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostSingletonSimonLiebPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostSingletonSimonLiebLocalizationPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostSingletonSimonLiebLocalization_of_singletonSimonLieb h

/--
[finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLiebComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLiebComparison_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostSingletonSimonLiebComparisonPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLiebComparison h

/--
[finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLieb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLieb_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostSingletonSimonLiebPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLieb h

/--
[finiteQ2SimonBoundaryGhostComparison_of_scalarBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_scalarBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_scalarBound h

/--
[finiteQ2SimonBoundaryGhostComparison_of_scalarCurrentBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_scalarCurrentBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCurrentBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_scalarCurrentBound h

/--
[finiteQ2SimonBoundaryGhostComparison_of_scalarCurrentSumBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_scalarCurrentSumBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCurrentSumBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_scalarCurrentSumBound h

/--
[finiteQ2SimonBoundaryGhostComparison_of_sourcePairBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_sourcePairBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_sourcePairBound h

/--
[finiteQ2SimonBoundaryGhostComparison_of_edgeCopyBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_edgeCopyBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_edgeCopyBound h

/--
[finiteQ2SimonBoundaryGhostComparison_of_emptyCollapsedBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_emptyCollapsedBound_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_emptyCollapsedBound h

/--
[finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive h

/--
[finiteQ2SimonBoundaryGhostComparison_of_decrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_decrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_decrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexSigmaFiniteSubcaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexSigmaFiniteSubcaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexSigmaFiniteSubcaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexSigmaFiniteLabelCaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexSigmaFiniteLabelCaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexSigmaFiniteLabelCaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_globalDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_globalDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_globalDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_sigmaDecrementedSourceAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_sigmaDecrementedSourceAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_sigmaDecrementedSourceAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_sigmaFiniteSubcaseAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_sigmaFiniteSubcaseAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_sigmaFiniteSubcaseAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryMultiplicityAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryMultiplicityAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryMultiplicityAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourcePairProfileAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourcePairProfileAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourcePairProfileAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberImageCardSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberImageCardSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberImageCardSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberDecomposedSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberDecomposedSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecomposedSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberDecomposedSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourcePairAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourcePairAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourcePairAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberUniformCardCapAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberUniformCardCapAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberUniformCardCapAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberUniformCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberUniformCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberUniformCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption h

/--
[finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLiebLocalization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLiebLocalization_eq
-- given
  (h : FiniteQ2SimonBoundaryGhostSingletonSimonLiebLocalizationPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLiebLocalization h

/--
[le_of_forall_pos_le_add_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma le_of_forall_pos_le_add_real_eq
  {a b : ℝ}
-- given
  (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) :
-- imply
  a ≤ b := by
-- proof
  apply StatMech.le_of_forall_pos_le_add_real h

/--
[finiteCurrentSimon_pointwise_of_boundaryGhostApprox_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteCurrentSimon_pointwise_of_boundaryGhostApprox_comparison_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (happrox : ∀ ε : ℝ, 0 < ε → ∃ H : ℝ, 0 ≤ H ∧ IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β (IsingFK.boxOrigin 3 n) ≤ finiteBoundaryGhostCurrentOnePoint 3 n β H + ε)
  (hcompare : ∀ H : ℝ, 0 ≤ H → finiteBoundaryGhostCurrentOnePoint 3 n β H ≤ finiteCurrentBoundaryTwoPointSum β n) :
-- imply
  IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β (IsingFK.boxOrigin 3 n) ≤ finiteCurrentBoundaryTwoPointSum β n := by
-- proof
  apply StatMech.finiteCurrentSimon_pointwise_of_boundaryGhostApprox_comparison happrox hcompare

/--
[finiteCurrentSimon_of_boundaryGhostApprox_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteCurrentSimon_of_boundaryGhostApprox_comparison_eq
-- given
  (happrox : FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
  (hcompare : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical := by
-- proof
  apply StatMech.finiteCurrentSimon_of_boundaryGhostApprox_comparison happrox hcompare

/--
[finiteCurrentSimon_of_boundaryGhostApprox_firstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteCurrentSimon_of_boundaryGhostApprox_firstExitPositive_eq
-- given
  (happrox : FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical := by
-- proof
  apply StatMech.finiteCurrentSimon_of_boundaryGhostApprox_firstExitPositive happrox hfirst

/--
[finiteExpectationJSimon_of_currentSimon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteExpectationJSimon_of_currentSimon_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryExpectationJPositiveSubcritical := by
-- proof
  apply StatMech.finiteExpectationJSimon_of_currentSimon hSimon

/--
[finiteIsingTwoPoint_boxGraph_eq_expectationJ_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteIsingTwoPoint_boxGraph_eq_expectationJ_symmDiff_eq
  {d n : ℕ}
  {β : ℝ}
  {x y : FK.boxVerts d n} :
-- imply
  (∑ σ : ConfigSpace (FK.boxVerts d n), Ising.isingProb (FK.boxGraph d n) β 0 σ * (Ising.spin σ x * Ising.spin σ y)) = Sharpness.expectationJ (FK.boxGraph d n) β (fun _ => 1) (({x} : Finset (FK.boxVerts d n)) ∆ {y}) := by
-- proof
  apply StatMech.finiteIsingTwoPoint_boxGraph_eq_expectationJ_symmDiff d n β x y

/--
[finiteIsingBoundaryTwoPointSum_eq_expectationJBoundarySum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteIsingBoundaryTwoPointSum_eq_expectationJBoundarySum_eq
  {β : ℝ}
  {n : ℕ} :
-- imply
  (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), ∑ σ : ConfigSpace (FK.boxVerts 3 n), Ising.isingProb (FK.boxGraph 3 n) β 0 σ * (Ising.spin σ (IsingFK.boxOrigin 3 n) * Ising.spin σ v)) = ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1) (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
-- proof
  apply StatMech.finiteIsingBoundaryTwoPointSum_eq_expectationJBoundarySum n

/--
[finiteIsingSimon_of_expectationJSimon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteIsingSimon_of_expectationJSimon_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryExpectationJPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical := by
-- proof
  apply StatMech.finiteIsingSimon_of_expectationJSimon hSimon

/--
[finiteIsingSimon_of_currentSimon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteIsingSimon_of_currentSimon_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical := by
-- proof
  apply StatMech.finiteIsingSimon_of_currentSimon hSimon

/--
[finiteIsingSimon_of_boundaryGhostApprox_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteIsingSimon_of_boundaryGhostApprox_comparison_eq
-- given
  (happrox : FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
  (hcompare : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical := by
-- proof
  apply StatMech.finiteIsingSimon_of_boundaryGhostApprox_comparison happrox hcompare

/--
[finiteIsingSimon_of_boundaryGhostApprox_firstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteIsingSimon_of_boundaryGhostApprox_firstExitPositive_eq
-- given
  (happrox : FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical := by
-- proof
  apply StatMech.finiteIsingSimon_of_boundaryGhostApprox_firstExitPositive happrox hfirst

/--
[finiteIsingBoundaryTwoPointSum_eq_freeFKBoundaryConnSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteIsingBoundaryTwoPointSum_eq_freeFKBoundaryConnSum_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβpos : 0 < β) :
-- imply
  (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), ∑ σ : ConfigSpace (FK.boxVerts 3 n), Ising.isingProb (FK.boxGraph 3 n) β 0 σ * (Ising.spin σ (IsingFK.boxOrigin 3 n) * Ising.spin σ v)) = ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n), ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) := by
-- proof
  apply StatMech.finiteIsingBoundaryTwoPointSum_eq_freeFKBoundaryConnSum hβpos n

/--
[finiteQ2_wiredOnePoint_eq_wiredFKBoundaryConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma finiteQ2_wiredOnePoint_eq_wiredFKBoundaryConn_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβpos : 0 < β)
  (hn : 1 ≤ n) :
-- imply
  IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β (IsingFK.boxOrigin 3 n) = ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxBdryConnEvent 3 n) := by
-- proof
  apply StatMech.finiteQ2_wiredOnePoint_eq_wiredFKBoundaryConn hβpos hn

/--
[freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon hSimon

/--
[freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_currentSimon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_currentSimon_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_currentSimon hSimon

/--
[freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_comparison_eq
-- given
  (happrox : FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
  (hcompare : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_comparison happrox hcompare

/--
[freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_firstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_firstExitPositive_eq
-- given
  (happrox : FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_firstExitPositive happrox hfirst

/--
[freeQ2BoundaryProfileSimonFreeSumPositiveSubcritical_of_eventually_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSumPositiveSubcritical_of_eventually_at_eq
-- given
  (hsimon : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryProfileSimonFreeSumAt β hβpos n) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSimonFreeSumPositiveSubcritical_of_eventually_at hsimon

/--
[freeQ2BoundaryProfileSimonFreeSum_of_finiteFK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_finiteFK_eq
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSimonFreeSum_of_finiteFK hfinite

/--
[freeQ2BoundaryProfileSimonFreeSumAt_of_finiteFKAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSumAt_of_finiteFKAt_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt β hβpos n) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumAt β hβpos n := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSimonFreeSumAt_of_finiteFKAt hfinite

/--
[freeQ2BoundaryProfileSimonFreeSum_of_boundaryGhostApprox_firstExitPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_boundaryGhostApprox_firstExitPositive_eq
-- given
  (happrox : FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSimonFreeSum_of_boundaryGhostApprox_firstExitPositive happrox hfirst

/--
[freeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical_of_eventually_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical_of_eventually_at_eq
-- given
  (hprojection : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryFreeVertexDoubleScaleProjectionAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical_of_eventually_at hprojection

/--
[boxVertTransverseHeight3_le_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertTransverseHeight3_le_two_mul_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n} :
-- imply
  boxVertTransverseHeight3 v ≤ 2 * n := by
-- proof
  apply StatMech.boxVertTransverseHeight3_le_two_mul v

/--
[boxVert_eq_of_hasCoords3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVert_eq_of_hasCoords3_eq
  {n : ℕ}
  {v w : FK.boxVerts 3 n}
  {x y z : ℤ}
-- given
  (hv : boxVertHasCoords3 v x y z)
  (hw : boxVertHasCoords3 w x y z) :
-- imply
  v = w := by
-- proof
  apply StatMech.boxVert_eq_of_hasCoords3 hv hw

/--
[boxVertOfCoords3_hasCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertOfCoords3_hasCoords_eq
  {n : ℕ}
  {x y z : ℤ}
-- given
  (hx : x.natAbs ≤ n)
  (hy : y.natAbs ≤ n)
  (hz : z.natAbs ≤ n) :
-- imply
  boxVertHasCoords3 (boxVertOfCoords3 n x y z hx hy hz) x y z := by
-- proof
  apply StatMech.boxVertOfCoords3_hasCoords n x y z hx hy hz

/--
[exists_boxVertHasCoords3_of_natAbs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma exists_boxVertHasCoords3_of_natAbs_le_eq
  {n : ℕ}
  {x y z : ℤ}
-- given
  (hx : x.natAbs ≤ n)
  (hy : y.natAbs ≤ n)
  (hz : z.natAbs ≤ n) :
-- imply
  ∃ w : FK.boxVerts 3 n, boxVertHasCoords3 w x y z := by
-- proof
  apply StatMech.exists_boxVertHasCoords3_of_natAbs_le hx hy hz

/--
[boxVertStrictSectorPredecessor3_hasCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertStrictSectorPredecessor3_hasCoords_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  boxVertHasCoords3 (boxVertStrictSectorPredecessor3 v hvwedge hlt) (n : ℤ) ((v : Lattice.Site 3) (1 : Fin 3)) (((v : Lattice.Site 3) (2 : Fin 3)) - 1) := by
-- proof
  apply StatMech.boxVertStrictSectorPredecessor3_hasCoords v hvwedge hlt

/--
[exists_boxVertHasCoords3_orderedWedge_strictSector_predZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma exists_boxVertHasCoords3_orderedWedge_strictSector_predZ_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  ∃ w : FK.boxVerts 3 n, boxVertHasCoords3 w (n : ℤ) ((v : Lattice.Site 3) (1 : Fin 3)) (((v : Lattice.Site 3) (2 : Fin 3)) - 1) := by
-- proof
  apply StatMech.exists_boxVertHasCoords3_orderedWedge_strictSector_predZ hvwedge hlt

/--
[boxVertStrictSectorYPredecessor3_hasCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertStrictSectorYPredecessor3_hasCoords_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3)))
  (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
-- imply
  boxVertHasCoords3 (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) (n : ℤ) (((v : Lattice.Site 3) (1 : Fin 3)) - 1) ((v : Lattice.Site 3) (2 : Fin 3)) := by
-- proof
  apply StatMech.boxVertStrictSectorYPredecessor3_hasCoords v hvwedge hlt hypos

/--
[exists_boxVertHasCoords3_orderedWedge_strictSector_predY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma exists_boxVertHasCoords3_orderedWedge_strictSector_predY_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3)))
  (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
-- imply
  ∃ w : FK.boxVerts 3 n, boxVertHasCoords3 w (n : ℤ) (((v : Lattice.Site 3) (1 : Fin 3)) - 1) ((v : Lattice.Site 3) (2 : Fin 3)) := by
-- proof
  apply StatMech.exists_boxVertHasCoords3_orderedWedge_strictSector_predY hvwedge hlt hypos

/--
[boxVertDiagonalPredecessor3_hasCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertDiagonalPredecessor3_hasCoords_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hheight : boxVertTransverseHeight3 v ≠ 0)
  (hnotlt : ¬ ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  boxVertHasCoords3 (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) (n : ℤ) (((v : Lattice.Site 3) (1 : Fin 3)) - 1) ((v : Lattice.Site 3) (2 : Fin 3)) := by
-- proof
  apply StatMech.boxVertDiagonalPredecessor3_hasCoords v hvwedge hheight hnotlt

/--
[exists_boxVertHasCoords3_orderedWedge_diagonal_predY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma exists_boxVertHasCoords3_orderedWedge_diagonal_predY_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hheight : boxVertTransverseHeight3 v ≠ 0)
  (hnotlt : ¬ ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  ∃ w : FK.boxVerts 3 n, boxVertHasCoords3 w (n : ℤ) (((v : Lattice.Site 3) (1 : Fin 3)) - 1) ((v : Lattice.Site 3) (2 : Fin 3)) := by
-- proof
  apply StatMech.exists_boxVertHasCoords3_orderedWedge_diagonal_predY hvwedge hheight hnotlt

/--
[boxVertStrictSectorPredecessor3_wedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertStrictSectorPredecessor3_wedge_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  boxVertPositiveXFaceOrderedWedge3 n (boxVertStrictSectorPredecessor3 v hvwedge hlt) := by
-- proof
  apply StatMech.boxVertStrictSectorPredecessor3_wedge v hvwedge hlt

/--
[boxVertStrictSectorPredecessor3_height_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertStrictSectorPredecessor3_height_lt_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  boxVertTransverseHeight3 (boxVertStrictSectorPredecessor3 v hvwedge hlt) < boxVertTransverseHeight3 v := by
-- proof
  apply StatMech.boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt

/--
[boxVertStrictSectorYPredecessor3_wedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertStrictSectorYPredecessor3_wedge_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3)))
  (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
-- imply
  boxVertPositiveXFaceOrderedWedge3 n (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
-- proof
  apply StatMech.boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos

/--
[boxVertStrictSectorYPredecessor3_height_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertStrictSectorYPredecessor3_height_lt_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3)))
  (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
-- imply
  boxVertTransverseHeight3 (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) < boxVertTransverseHeight3 v := by
-- proof
  apply StatMech.boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos

/--
[boxVertDiagonalPredecessor3_wedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertDiagonalPredecessor3_wedge_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hheight : boxVertTransverseHeight3 v ≠ 0)
  (hnotlt : ¬ ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  boxVertPositiveXFaceOrderedWedge3 n (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) := by
-- proof
  apply StatMech.boxVertDiagonalPredecessor3_wedge v hvwedge hheight hnotlt

/--
[boxVertDiagonalPredecessor3_height_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVertDiagonalPredecessor3_height_lt_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hheight : boxVertTransverseHeight3 v ≠ 0)
  (hnotlt : ¬ ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  boxVertTransverseHeight3 (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) < boxVertTransverseHeight3 v := by
-- proof
  apply StatMech.boxVertDiagonalPredecessor3_height_lt v hvwedge hheight hnotlt

/--
[freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
  {v w : FK.boxVerts 3 n}
  {x y z : ℤ}
-- given
  (hv : boxVertHasCoords3 v x y z)
  (hw : boxVertHasCoords3 w x y z) :
-- imply
  freeQ2DoubledFullOriginConnProb β hβpos n v = freeQ2DoubledFullOriginConnProb β hβpos n w := by
-- proof
  apply StatMech.freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3 hv hw

/--
[freeQ2DoubledEndpointDetourProb_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2DoubledEndpointDetourProb_le_boundary_eq
  {β : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβpos : 0 < β)
  (hn : 1 ≤ n) :
-- imply
  freeQ2DoubledEndpointDetourProb β hβpos n v ≤ freeFiniteVolumeOriginBoundaryConnectionOfBetaQ2InVolume β hβpos (2 * n) n := by
-- proof
  apply StatMech.freeQ2DoubledEndpointDetourProb_le_boundary β hβpos n v hn

/--
[freeQ2DoubledEndpointDetourProb_le_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2DoubledEndpointDetourProb_le_profile_eq
  {β : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβpos : 0 < β)
  (hn : 1 ≤ n) :
-- imply
  freeQ2DoubledEndpointDetourProb β hβpos n v ≤ freeQ2BoundaryProfileOfBeta β hβpos n := by
-- proof
  apply StatMech.freeQ2DoubledEndpointDetourProb_le_profile β hβpos n v hn

/--
[boxConnEvent_subset_outerBoxConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxConnEvent_subset_outerBoxConnEvent_eq
  {d n M : ℕ}
  {x y : FK.boxVerts d n}
-- given
  (h : n ≤ M) :
-- imply
  FK.boxConnEvent d n x y ⊆ FK.boxConnEvent d M (FK.boxVertInclLE d h x) (FK.boxVertInclLE d h y) := by
-- proof
  apply StatMech.boxConnEvent_subset_outerBoxConnEvent h x y

/--
[freeQ2DoubledInnerOriginConnProb_le_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2DoubledInnerOriginConnProb_le_full_eq
  {β : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβpos : 0 < β) :
-- imply
  freeQ2DoubledInnerOriginConnProb β hβpos n v ≤ freeQ2DoubledFullOriginConnProb β hβpos n v := by
-- proof
  apply StatMech.freeQ2DoubledInnerOriginConnProb_le_full β hβpos n v

/--
[freeQ2DoubledFullOriginConnProb_eq_inner_add_detour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2DoubledFullOriginConnProb_eq_inner_add_detour_eq
  {β : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβpos : 0 < β) :
-- imply
  freeQ2DoubledFullOriginConnProb β hβpos n v = freeQ2DoubledInnerOriginConnProb β hβpos n v + freeQ2DoubledEndpointDetourProb β hβpos n v := by
-- proof
  apply StatMech.freeQ2DoubledFullOriginConnProb_eq_inner_add_detour β hβpos n v

/--
[freeQ2DoubledInnerOriginConnProb_le_inner_add_error_of_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2DoubledInnerOriginConnProb_le_inner_add_error_of_full_eq
  {β : ℝ}
  {n : ℕ}
  {v w : FK.boxVerts 3 n}
  {ε : ℝ}
-- given
  (hβpos : 0 < β)
  (hfull : freeQ2DoubledFullOriginConnProb β hβpos n v ≤ freeQ2DoubledFullOriginConnProb β hβpos n w)
  (hdetour : freeQ2DoubledFullOriginConnProb β hβpos n w ≤ freeQ2DoubledInnerOriginConnProb β hβpos n w + ε) :
-- imply
  freeQ2DoubledInnerOriginConnProb β hβpos n v ≤ freeQ2DoubledInnerOriginConnProb β hβpos n w + ε := by
-- proof
  apply StatMech.freeQ2DoubledInnerOriginConnProb_le_inner_add_error_of_full β hβpos n v w ε hfull hdetour

/--
[freeQ2DoubledInnerOriginConnProb_le_inner_add_detour_of_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2DoubledInnerOriginConnProb_le_inner_add_detour_of_full_eq
  {β : ℝ}
  {n : ℕ}
  {v w : FK.boxVerts 3 n}
-- given
  (hβpos : 0 < β)
  (hfull : freeQ2DoubledFullOriginConnProb β hβpos n v ≤ freeQ2DoubledFullOriginConnProb β hβpos n w) :
-- imply
  freeQ2DoubledInnerOriginConnProb β hβpos n v ≤ freeQ2DoubledInnerOriginConnProb β hβpos n w + freeQ2DoubledEndpointDetourProb β hβpos n w := by
-- proof
  apply StatMech.freeQ2DoubledInnerOriginConnProb_le_inner_add_detour_of_full β hβpos n v w hfull

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_body_of_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_body_of_at_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepAt β hβpos n) :
-- imply
  ∀ v : FK.boxVerts 3 n, boxVertPositiveXFaceOrderedWedge3 n v → boxVertTransverseHeight3 v ≠ 0 → let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3) let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3) if y < z then ∃ w : FK.boxVerts 3 n, boxVertHasCoords3 w (n : ℤ) y (z - 1) ∧ ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) w) else ∃ w : FK.boxVerts 3 n, boxVertHasCoords3 w (n : ℤ) (y - 1) z ∧ ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) w) := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_body_of_at hstep

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_local_eq
-- given
  (hlocal : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_local hlocal

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches_eq
-- given
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_branches hstrict hdiag

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt_of_predecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt_of_predecessorComparison_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorPredecessorComparisonAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt β hβpos n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepAt_of_predecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt_of_predecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt_of_predecessorComparison_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalPredecessorComparisonAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt β hβpos n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepAt_of_predecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStep_of_predecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStep_of_predecessorComparison_eq
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorPredecessorComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStep_of_predecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStep_of_predecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStep_of_predecessorComparison_eq
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalPredecessorComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStep_of_predecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_predecessorComparisons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_predecessorComparisons_eq
-- given
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalPredecessorComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStep_of_predecessorComparisons hstrict hdiag

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt_of_fullCoordinateComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt_of_fullCoordinateComparison_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt β hβpos n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt_of_fullCoordinateComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt_of_fullCoordinateComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt_of_fullCoordinateComparison_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt β hβpos n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt_of_fullCoordinateComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt_of_fullPredecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt_of_fullPredecessorComparison_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt β hβpos n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonAt_of_fullPredecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt_of_fullPredecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt_of_fullPredecessorComparison_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt β hβpos n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonAt_of_fullPredecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_local_eq
-- given
  (hlocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_local hlocal

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_local_eq
-- given
  (hlocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_local hlocal

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparison_of_fullCoordinateComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparison_of_fullCoordinateComparison_eq
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparison_of_fullCoordinateComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparison_of_fullCoordinateComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparison_of_fullCoordinateComparison_eq
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparison_of_fullCoordinateComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparison_of_fullPredecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparison_of_fullPredecessorComparison_eq
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparison_of_fullPredecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparison_of_fullPredecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparison_of_fullPredecessorComparison_eq
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparison_of_fullPredecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullPredecessorComparisons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullPredecessorComparisons_eq
-- given
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullPredecessorComparisons hstrict hdiag

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullCoordinateComparisons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullCoordinateComparisons_eq
-- given
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullCoordinateComparisons hstrict hdiag

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBound_of_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBound_of_profileDoubleScale_eq
-- given
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBoundPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBound_of_profileDoubleScale hprofile

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialError_of_fullStrictDescent_detourPolynomialBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialError_of_fullStrictDescent_detourPolynomialBound_eq
-- given
  (hfull : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical)
  (hdetour : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBoundPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialErrorPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialError_of_fullStrictDescent_detourPolynomialBound hfull hdetour

/--
[exists_boxSym_lift_positiveXFace_of_boxBoundary3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma exists_boxSym_lift_positiveXFace_of_boxBoundary3_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : FK.boxBoundary 3 n v) :
-- imply
  ∃ S : FK.BoxSym 3, ((S.lift n v : Lattice.Site 3) 0 = (n : ℤ)) := by
-- proof
  apply StatMech.exists_boxSym_lift_positiveXFace_of_boxBoundary3 n v hv

/--
[boxBoundary3_of_positiveXFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxBoundary3_of_positiveXFace_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hn : 0 < n)
  (hv : (v : Lattice.Site 3) 0 = (n : ℤ)) :
-- imply
  FK.boxBoundary 3 n v := by
-- proof
  apply StatMech.boxBoundary3_of_positiveXFace hn v hv

/--
[exists_boxSym_lift_positiveXFaceOrderedWedge_of_positiveXFace3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma exists_boxSym_lift_positiveXFaceOrderedWedge_of_positiveXFace3_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : (v : Lattice.Site 3) 0 = (n : ℤ)) :
-- imply
  ∃ S : FK.BoxSym 3, boxVertPositiveXFaceOrderedWedge3 n (S.lift n v) := by
-- proof
  apply StatMech.exists_boxSym_lift_positiveXFaceOrderedWedge_of_positiveXFace3 n v hv

/--
[freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_doubledBoxProjection_eq
-- given
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_doubledBoxProjection hprojection

/--
[freeQ2BoundaryFreeVertex_le_sameVertexDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertex_le_sameVertexDoubleScale_eq
  {β : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hβpos : 0 < β) :
-- imply
  ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertex_le_sameVertexDoubleScale β hβpos n v

/--
[twoPointFun_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma twoPointFun_boxSym_eq
  {d : ℕ}
  {S : FK.BoxSym d}
  {n : ℕ}
  {p q : ℝ}
  {x y : FK.boxVerts d n} :
-- imply
  FK.twoPointFun (FK.boxGraph d n) p q (S.lift n x) (S.lift n y) = FK.twoPointFun (FK.boxGraph d n) p q x y := by
-- proof
  apply StatMech.twoPointFun_boxSym S n p q x y

/--
[freeFiniteMeasure_real_boxConnEvent_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_boxConnEvent_boxSym_eq
  {d : ℕ}
  {S : FK.BoxSym d}
  {n : ℕ}
  {p q : ℝ}
  {x y : FK.boxVerts d n}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ((FK.freeFiniteMeasure d n hp hp1 hq) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n (S.lift n x) (S.lift n y)) = ((FK.freeFiniteMeasure d n hp hp1 hq) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n x y) := by
-- proof
  apply StatMech.freeFiniteMeasure_real_boxConnEvent_boxSym S n hp hp1 hq x y

/--
[boxRestrictLE_reCfg_boxSym_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxRestrictLE_reCfg_boxSym_symm_eq
  {d n M : ℕ}
  {S : FK.BoxSym d}
  {ω : ConfigSpace (Sym2 (FK.boxVerts d M))}
-- given
  (h : n ≤ M) :
-- imply
  FK.boxRestrictLE d h (FK.reCfg (S.lift M).symm ω) = FK.reCfg (S.lift n).symm (FK.boxRestrictLE d h ω) := by
-- proof
  apply StatMech.boxRestrictLE_reCfg_boxSym_symm h S ω

/--
[freeFiniteMeasure_real_innerBoxConnEvent_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_innerBoxConnEvent_boxSym_eq
  {d n M : ℕ}
  {S : FK.BoxSym d}
  {p q : ℝ}
  {x y : FK.boxVerts d n}
-- given
  (h : n ≤ M)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ((FK.freeFiniteMeasure d M hp hp1 hq) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n (S.lift n x) (S.lift n y)) = ((FK.freeFiniteMeasure d M hp hp1 hq) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n x y) := by
-- proof
  apply StatMech.freeFiniteMeasure_real_innerBoxConnEvent_boxSym h S hp hp1 hq x y

/--
[boxSym_fixes_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxSym_fixes_origin_eq
  {d : ℕ}
  {S : FK.BoxSym d} :
-- imply
  S.τ (StatMech.Percolation.origin d) = StatMech.Percolation.origin d := by
-- proof
  apply StatMech.boxSym_fixes_origin S

/--
[boxSym_lift_boxOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxSym_lift_boxOrigin_eq
  {d : ℕ}
  {S : FK.BoxSym d}
  {n : ℕ} :
-- imply
  S.lift n (IsingFK.boxOrigin d n) = IsingFK.boxOrigin d n := by
-- proof
  apply StatMech.boxSym_lift_boxOrigin S n

/--
[freeFiniteMeasure_real_boxOriginConnEvent_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_boxOriginConnEvent_boxSym_eq
  {d : ℕ}
  {S : FK.BoxSym d}
  {n : ℕ}
  {p q : ℝ}
  {y : FK.boxVerts d n}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ((FK.freeFiniteMeasure d n hp hp1 hq) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n (IsingFK.boxOrigin d n) (S.lift n y)) = ((FK.freeFiniteMeasure d n hp hp1 hq) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n (IsingFK.boxOrigin d n) y) := by
-- proof
  apply StatMech.freeFiniteMeasure_real_boxOriginConnEvent_boxSym S n hp hp1 hq y

/--
[freeFiniteMeasure_real_innerBoxOriginConnEvent_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_innerBoxOriginConnEvent_boxSym_eq
  {d n M : ℕ}
  {S : FK.BoxSym d}
  {p q : ℝ}
  {y : FK.boxVerts d n}
-- given
  (h : n ≤ M)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ((FK.freeFiniteMeasure d M hp hp1 hq) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n (IsingFK.boxOrigin d n) (S.lift n y)) = ((FK.freeFiniteMeasure d M hp hp1 hq) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))).real (FK.boxConnEvent d n (IsingFK.boxOrigin d n) y) := by
-- proof
  apply StatMech.freeFiniteMeasure_real_innerBoxOriginConnEvent_boxSym h S hp hp1 hq y

/--
[freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_positiveXFaceOrderedWedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_positiveXFaceOrderedWedge_eq
-- given
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjection_of_positiveXFaceOrderedWedge hprojection

/--
[freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFace_eq
-- given
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFace hprojection

/--
[freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedge_eq
-- given
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedge hprojection

/--
[freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_doubledBoxProjection_eq
-- given
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_doubledBoxProjection hprojection

/--
[freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge_eq
-- given
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge hprojection

/--
[freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFace_eq
-- given
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFace hprojection

/--
[freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge_eq
-- given
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubledBoxPolynomialProjection_of_positiveXFaceOrderedWedge hprojection

/--
[freeQ2BoundaryFreeVertexDoubleScaleProjection_of_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubleScaleProjection_of_doubledBoxProjection_eq
-- given
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubleScaleProjection_of_doubledBoxProjection hprojection

/--
[freeQ2BoundaryFreeVertexDoubleScaleProjection_xAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubleScaleProjection_xAxis_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβpos : 0 < β) :
-- imply
  ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) (ising3DXAxisBoxVertex n)) ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubleScaleProjection_xAxis β hβpos n

/--
[freeQ2BoundaryFreeVertexDoubleScaleProjection_of_boxSym_xAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubleScaleProjection_of_boxSym_xAxis_eq
  {β : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {S : FK.BoxSym 3}
-- given
  (hβpos : 0 < β)
  (hv : S.lift n v = ising3DXAxisBoxVertex n) :
-- imply
  ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubleScaleProjection_of_boxSym_xAxis β hβpos n v S hv

/--
[freeQ2BoundaryFreeVertexDoubledBoxProjection_xAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubledBoxProjection_xAxis_eq
  {β : ℝ}
  {n : ℕ}
-- given
  (hβpos : 0 < β) :
-- imply
  ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) (ising3DXAxisBoxVertex n)) ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubledBoxProjection_xAxis β hβpos n

/--
[boxVert_eq_xAxis_of_positiveXFaceOrderedWedge_height_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxVert_eq_xAxis_of_positiveXFaceOrderedWedge_height_zero_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : boxVertPositiveXFaceOrderedWedge3 n v)
  (hheight : boxVertTransverseHeight3 v = 0) :
-- imply
  v = ising3DXAxisBoxVertex n := by
-- proof
  apply StatMech.boxVert_eq_xAxis_of_positiveXFaceOrderedWedge_height_zero hv hheight

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescent_of_coordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescent_of_coordinateStep_eq
-- given
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescentDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescent_of_coordinateStep hstep

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_strictDescent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_strictDescent_eq
-- given
  (hdescent : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescentDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_strictDescent hdescent

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_coordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_coordinateStep_eq
-- given
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjection_of_coordinateStep hstep

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_additiveStrictDescentPolynomialError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_additiveStrictDescentPolynomialError_eq
-- given
  (hdescent : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialErrorPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_additiveStrictDescentPolynomialError hdescent

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullStrictDescent_detourPolynomialBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullStrictDescent_detourPolynomialBound_eq
-- given
  (hfull : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical)
  (hdetour : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBoundPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullStrictDescent_detourPolynomialBound hfull hdetour

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_detourPolynomialBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_detourPolynomialBound_eq
-- given
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
  (hdetour : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBoundPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_detourPolynomialBound hstrict hdiag hdetour

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_profileDoubleScale_eq
-- given
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullPredecessorComparisons_profileDoubleScale hstrict hdiag hprofile

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullCoordinateComparisons_profileDoubleScale hstrict hdiag hprofile

/--
[freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedgeStrictDescent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedgeStrictDescent_eq
-- given
  (hdescent : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictDescentDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedgeStrictDescent hdescent

/--
[freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubledBoxProjection_of_positiveXFaceOrderedWedgeCoordinateStep hstep

/--
[freeQ2BoundaryFreeVertexDoubledBoxProjection_of_boxSym_xAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexDoubledBoxProjection_of_boxSym_xAxis_eq
  {β : ℝ}
  {n : ℕ}
  {v : FK.boxVerts 3 n}
  {S : FK.BoxSym 3}
-- given
  (hβpos : 0 < β)
  (hv : S.lift n v = ising3DXAxisBoxVertex n) :
-- imply
  ((FK.freeFiniteMeasure 3 (2 * n) (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)) : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) ≤ freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n := by
-- proof
  apply StatMech.freeQ2BoundaryFreeVertexDoubledBoxProjection_of_boxSym_xAxis β hβpos n v S hv

/--
[freeQ2BoundaryProfileDoubleScaleAt_of_simonFreeSumAt_projectionAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScaleAt_of_simonFreeSumAt_projectionAt_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumAt β hβpos n)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionAt β hβpos n) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScaleAt_of_simonFreeSumAt_projectionAt hsimon hprojection

/--
[freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_simonFreeSumAt_projectionAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_simonFreeSumAt_projectionAt_eq
-- given
  (hsimon : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryProfileSimonFreeSumAt β hβpos n)
  (hprojection : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryFreeVertexDoubleScaleProjectionAt β hβpos n) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_simonFreeSumAt_projectionAt hsimon hprojection

/--
[freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_finiteFKAt_projectionAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_finiteFKAt_projectionAt_eq
-- given
  (hfinite : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt β hβpos n)
  (hprojection : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in atTop, FreeQ2BoundaryFreeVertexDoubleScaleProjectionAt β hβpos n) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_finiteFKAt_projectionAt hfinite hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_projection_eq
-- given
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_projection hsimon hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_doubledBoxProjection_eq
-- given
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_doubledBoxProjection hsimon hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceProjection_eq
-- given
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceProjection hsimon hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeProjection hsimon hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep hsimon hstep

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_projection_eq
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_projection hfinite hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_doubledBoxProjection_eq
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_doubledBoxProjection hfinite hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceProjection_eq
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceProjection hfinite hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection hfinite hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep hfinite hstep

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_projection_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_projection hSimon hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_doubledBoxProjection_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_doubledBoxProjection hSimon hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceProjection_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceProjection hSimon hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection hSimon hprojection

/--
[freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep hSimon hstep

/--
[freeQ2BoundaryProfileDoubleScale_of_vertexDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileDoubleScale_of_vertexDoubleScale_eq
-- given
  (hcompare : FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileDoubleScale_of_vertexDoubleScale hcompare

/--
[freeQ2BoundaryVertexScaledPolynomial_of_doubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexScaledPolynomial_of_doubleScale_eq
-- given
  (hcompare : FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexScaledPolynomial_of_doubleScale hcompare

/--
[freeQ2BoundaryVertexFiniteVolumeComparisonToXAxis_of_finiteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexFiniteVolumeComparisonToXAxis_of_finiteVolumePolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexFiniteVolumeComparisonToXAxis_of_finiteVolumePolynomial hcompare

/--
[freeQ2BoundaryProfileFiniteVolumeComparison_of_boundaryVertexFiniteVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteVolumeComparison_of_boundaryVertexFiniteVolume_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileFiniteVolumeComparison_of_boundaryVertexFiniteVolume hcompare

/--
[freeQ2BoundaryProfileFiniteVolumePolynomial_of_boundaryVertexPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileFiniteVolumePolynomial_of_boundaryVertexPolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileFiniteVolumePolynomial_of_boundaryVertexPolynomial hcompare

/--
[freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_boundaryVertexScaledPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_boundaryVertexScaledPolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryVertexScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_boundaryVertexScaledPolynomial hcompare

/--
[freeQ2BoundaryProfileScaledPolynomial_of_vertexDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_vertexDoubleScale_eq
-- given
  (hcompare : FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_vertexDoubleScale hcompare

/--
[freeQ2BoundaryProfileScaledPolynomial_of_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_profileDoubleScale_eq
-- given
  (hcompare : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_profileDoubleScale hcompare

/--
[freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_doubledBoxPolynomialProjection_eq
-- given
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_doubledBoxPolynomialProjection hsimon hprojection

/--
[freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection_eq
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection hfinite hprojection

/--
[freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection hsimon hprojection

/--
[freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection hfinite hprojection

/--
[freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_doubledBoxPolynomialProjection_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_doubledBoxPolynomialProjection hSimon hprojection

/--
[freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection hSimon hprojection

/--
[freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale hsimon hstrict hdiag hprofile

/--
[freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale hfinite hstrict hdiag hprofile

/--
[freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledPolynomial_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale hSimon hstrict hdiag hprofile

/--
[freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_boundaryVertexPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_boundaryVertexPolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_boundaryVertexPolynomial hcompare

/--
[freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_boundaryVertexPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_boundaryVertexPolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_boundaryVertexPolynomial hcompare

/--
[freeQ2BoundaryVertexSubexpComparisonToXAxis_of_finiteVolumeComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexSubexpComparisonToXAxis_of_finiteVolumeComparison_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexSubexpComparisonToXAxis_of_finiteVolumeComparison hcompare

/--
[freeQ2BoundaryVertexPolynomialComparisonToXAxis_of_finiteVolumePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPolynomialComparisonToXAxis_of_finiteVolumePolynomial_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPolynomialComparisonToXAxis_of_finiteVolumePolynomial hcompare

/--
[freeQ2BoundaryVertexPointwise_of_subexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_subexpComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_subexpComparisonToXAxis hcompare

/--
[freeQ2BoundaryVertexPointwise_of_polynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_polynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_polynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryVertexPointwise_of_finiteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_finiteVolumeComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_finiteVolumeComparisonToXAxis hcompare

/--
[freeQ2BoundaryVertexPointwise_of_finiteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_finiteVolumePolynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_finiteVolumePolynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryVertexPointwise_of_envelopeAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_envelopeAtLeastMass_eq
-- given
  (henv : FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_envelopeAtLeastMass henv

/--
[boxBoundary3_surfaceVec_face_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma boxBoundary3_surfaceVec_face_cases_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hv : FK.boxBoundary 3 n v) :
-- imply
  let x : ℝ := ((v : Lattice.Site 3) 0 : ℝ) let y : ℝ := ((v : Lattice.Site 3) 1 : ℝ) let z : ℝ := ((v : Lattice.Site 3) 2 : ℝ) x = (n : ℝ) ∨ x = -(n : ℝ) ∨ y = (n : ℝ) ∨ y = -(n : ℝ) ∨ z = (n : ℝ) ∨ z = -(n : ℝ) := by
-- proof
  apply StatMech.boxBoundary3_surfaceVec_face_cases n v hv

/--
[freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper htension

/--
[freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper htension

/--
[freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate_eq
-- given
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate hdir

/--
[freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_convexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_convexSurfaceTensionUpper htension

/--
[freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_actualConvexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_actualConvexSurfaceTensionUpper htension

/--
[freeQ2BoundaryVertexEpsilonRate_of_polynomialRateWithXAxisLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexEpsilonRate_of_polynomialRateWithXAxisLogRate_eq
-- given
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexEpsilonRatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexEpsilonRate_of_polynomialRateWithXAxisLogRate hrate

/--
[freeQ2BoundaryVertexEpsilonRate_of_directionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexEpsilonRate_of_directionalRate_eq
-- given
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexEpsilonRatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexEpsilonRate_of_directionalRate hdir

/--
[freeQ2BoundaryVertexEpsilonRate_of_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexEpsilonRate_of_convexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexEpsilonRatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexEpsilonRate_of_convexSurfaceTensionUpper htension

/--
[freeQ2BoundaryVertexEpsilonRate_of_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexEpsilonRate_of_actualConvexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexEpsilonRatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexEpsilonRate_of_actualConvexSurfaceTensionUpper htension

/--
[freeQ2BoundaryVertexPolynomialAtLeastMass_of_polynomialRateWithXAxisLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPolynomialAtLeastMass_of_polynomialRateWithXAxisLogRate_eq
-- given
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
-- imply
  FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPolynomialAtLeastMass_of_polynomialRateWithXAxisLogRate hrate

/--
[freeQ2BoundaryVertexPointwise_of_polynomialAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_polynomialAtLeastMass_eq
-- given
  (hpoly : FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_polynomialAtLeastMass hpoly

/--
[freeQ2BoundaryVertexPointwise_of_polynomialRateWithXAxisLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_polynomialRateWithXAxisLogRate_eq
-- given
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_polynomialRateWithXAxisLogRate hrate

/--
[freeQ2BoundaryVertexPointwise_of_directionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_directionalRate_eq
-- given
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_directionalRate hdir

/--
[freeQ2BoundaryVertexPointwise_of_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_convexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_convexSurfaceTensionUpper htension

/--
[freeQ2BoundaryVertexPointwise_of_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryVertexPointwise_of_actualConvexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryVertexPointwise_of_actualConvexSurfaceTensionUpper htension

/--
[freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexPointwise_eq
-- given
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_boundaryVertexPointwise hprofile

/--
[freeQ2BoundaryProfileSubexpComparisonToXAxis_of_boundaryVertexSubexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpComparisonToXAxis_of_boundaryVertexSubexpComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpComparisonToXAxis_of_boundaryVertexSubexpComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpComparisonToXAxis_of_polynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpComparisonToXAxis_of_polynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpComparisonToXAxis_of_polynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumeComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumeComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumePolynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpComparisonToXAxis_of_finiteVolumePolynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_subexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_subexpComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_subexpComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_polynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_polynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_polynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_finiteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_finiteVolumeComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_finiteVolumeComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_finiteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_finiteVolumePolynomialComparisonToXAxis_eq
-- given
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_finiteVolumePolynomialComparisonToXAxis hcompare

/--
[freeQ2BoundaryProfileSubexpSameMass_of_envelopeAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_envelopeAtLeastMass_eq
-- given
  (henv : FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_envelopeAtLeastMass henv

/--
[freeQ2BoundaryProfileSubexpSameMass_of_polynomialAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_polynomialAtLeastMass_eq
-- given
  (hpoly : FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_polynomialAtLeastMass hpoly

/--
[freeQ2BoundaryProfileSubexpSameMass_of_polynomialRateWithXAxisLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_polynomialRateWithXAxisLogRate_eq
-- given
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_polynomialRateWithXAxisLogRate hrate

/--
[freeQ2BoundaryProfileSubexpSameMass_of_directionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_directionalRate_eq
-- given
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_directionalRate hdir

/--
[freeQ2BoundaryProfileSubexpSameMass_of_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_convexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_convexSurfaceTensionUpper htension

/--
[freeQ2BoundaryProfileSubexpSameMass_of_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSubexpSameMass_of_actualConvexSurfaceTensionUpper_eq
-- given
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileSubexpSameMass_of_actualConvexSurfaceTensionUpper htension

/--
[freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided_eq
-- given
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreeQ2FixedInnerTwoSidedPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay

/--
[freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_profile_eq
-- given
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreeQ2FixedInnerProfileSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_profile hfixed hprofile

/--
[freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_weak](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_weak_eq
-- given
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical) :
-- imply
  FreeQ2FixedInnerProfileSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2FixedInnerProfileSameMassPositiveSubcritical_of_fixedInner_weak hfixed

/--
[freeQ2BoundaryProfileForFixedInnerSameMass_of_subexponentialProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileForFixedInnerSameMass_of_subexponentialProfile_eq
-- given
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical := by
-- proof
  apply StatMech.freeQ2BoundaryProfileForFixedInnerSameMass_of_subexponentialProfile hprofile

/--
[freeQ2ProfileSeparatePositiveSubcritical_of_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparatePositiveSubcritical_of_components_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparatePositiveSubcritical_of_components hlim hsameMass hcombine

/--
[freeQ2ProfileSeparatePositiveSubcritical_of_splitComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparatePositiveSubcritical_of_splitComponents_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparatePositiveSubcritical_of_splitComponents hlim hfixed hprofile hcombine

/--
[freeQ2ProfileSeparate_of_freeFVQ2TwoSided_profile_combine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_freeFVQ2TwoSided_profile_combine_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_freeFVQ2TwoSided_profile_combine hlim hdecay hprofile hcombine

/--
[freeQ2ProfileSeparatePositiveSubcritical_of_splitSubexpProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparatePositiveSubcritical_of_splitSubexpProfile_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparatePositiveSubcritical_of_splitSubexpProfile hlim hfixed hprofile

/--
[freeQ2ProfileSeparatePositiveSubcritical_of_freeFVQ2TwoSided_splitSubexpProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparatePositiveSubcritical_of_freeFVQ2TwoSided_splitSubexpProfile_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparatePositiveSubcritical_of_freeFVQ2TwoSided_splitSubexpProfile hlim hdecay hprofile

/--
[freeQ2ProfileSeparate_of_boundaryVertexPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_boundaryVertexPointwise_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_boundaryVertexPointwise hlim hfixed hprofile

/--
[freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_profileSubexpComparisonToXAxis hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_profilePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_profilePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_profilePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_profileFiniteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_profileFiniteVolumeComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_profileFiniteVolumeComparisonToXAxis hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_profileFiniteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_profileFiniteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_profileFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_vertexDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_vertexDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_vertexDoubleScale hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_profileDoubleScale hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_simonFreeSum_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_simonFreeSum_doubledBoxPolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_simonFreeSum_doubledBoxPolynomialProjection hlim hfixed hsimon hprojection

/--
[freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection hlim hfixed hsimon hprojection

/--
[freeQ2ProfileSeparate_of_simonFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_simonFreeSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_simonFreeSum_projection hlim hfixed hsimon hprojection

/--
[freeQ2ProfileSeparate_of_simonFreeSum_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_simonFreeSum_doubledBoxProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_simonFreeSum_doubledBoxProjection hlim hfixed hsimon hprojection

/--
[freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceProjection hlim hfixed hsimon hprojection

/--
[freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeProjection hlim hfixed hsimon hprojection

/--
[freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep hlim hfixed hsimon hstep

/--
[freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches hlim hfixed hsimon hstrict hdiag

/--
[freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection hlim hfixed hfinite hprojection

/--
[freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection hlim hfixed hfinite hprojection

/--
[freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_projection hlim hfixed hfinite hprojection

/--
[freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_doubledBoxProjection hlim hfixed hfinite hprojection

/--
[freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceProjection hlim hfixed hfinite hprojection

/--
[freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection hlim hfixed hfinite hprojection

/--
[freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep hlim hfixed hfinite hstep

/--
[freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches hlim hfixed hfinite hstrict hdiag

/--
[freeQ2ProfileSeparate_of_finiteIsingSimon_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteIsingSimon_doubledBoxPolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteIsingSimon_doubledBoxPolynomialProjection hlim hfixed hSimon hprojection

/--
[freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection hlim hfixed hSimon hprojection

/--
[freeQ2ProfileSeparate_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale hlim hfixed hsimon hstrict hdiag hprofile

/--
[freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale hlim hfixed hfinite hstrict hdiag hprofile

/--
[freeQ2ProfileSeparate_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale hlim hfixed hSimon hstrict hdiag hprofile

/--
[freeQ2ProfileSeparate_of_finiteIsingSimon_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteIsingSimon_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteIsingSimon_projection hlim hfixed hSimon hprojection

/--
[freeQ2ProfileSeparate_of_finiteIsingSimon_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteIsingSimon_doubledBoxProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteIsingSimon_doubledBoxProjection hlim hfixed hSimon hprojection

/--
[freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceProjection hlim hfixed hSimon hprojection

/--
[freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection hlim hfixed hSimon hprojection

/--
[freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep hlim hfixed hSimon hstep

/--
[freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches hlim hfixed hSimon hstrict hdiag

/--
[freeQ2ProfileSeparate_of_subexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_subexpComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_subexpComparisonToXAxis hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_polynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_polynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_polynomialComparisonToXAxis hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_finiteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteVolumeComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteVolumeComparisonToXAxis hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_finiteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_finiteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_finiteVolumePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freeQ2ProfileSeparate_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis hlim hdecay hcompare

/--
[freeQ2ProfileSeparate_of_envelopeAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_envelopeAtLeastMass_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (henv : FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_envelopeAtLeastMass hlim hfixed henv

/--
[freeQ2ProfileSeparate_of_polynomialAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_polynomialAtLeastMass_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hpoly : FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_polynomialAtLeastMass hlim hfixed hpoly

/--
[freeQ2ProfileSeparate_of_polynomialRateWithXAxisLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_polynomialRateWithXAxisLogRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_polynomialRateWithXAxisLogRate hlim hfixed hrate

/--
[freeQ2ProfileSeparate_of_directionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_directionalRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_directionalRate hlim hfixed hdir

/--
[freeQ2ProfileSeparate_of_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_convexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_convexSurfaceTensionUpper hlim hfixed htension

/--
[freeQ2ProfileSeparate_of_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_actualConvexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_actualConvexSurfaceTensionUpper hlim hfixed htension

/--
[freeQ2ProfileSeparate_of_freeFVQ2TwoSided_boundaryPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_freeFVQ2TwoSided_boundaryPointwise_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_freeFVQ2TwoSided_boundaryPointwise hlim hdecay hprofile

/--
[freeQ2ProfileSeparate_of_freeFVQ2TwoSided_subexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freeQ2ProfileSeparate_of_freeFVQ2TwoSided_subexpComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2ProfileSeparatePositiveSubcritical := by
-- proof
  apply StatMech.freeQ2ProfileSeparate_of_freeFVQ2TwoSided_subexpComparisonToXAxis hlim hdecay hcompare

/--
[freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine

/--
[freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hsameMass : FreeQ2FixedInnerProfileSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_components hlim hsameMass hcombine

/--
[freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitComponents_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitComponents hlim hfixed hprofile hcombine

/--
[freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitComponents_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileForFixedInnerSameMassPositiveSubcritical)
  (hcombine : FreeQ2ProfilePrefactorCombinationPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitComponents hlim hfixed hprofile hcombine

/--
[freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim hfixed hprofile

/--
[freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_splitSubexpProfile hlim hfixed hprofile

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_splitSubexpProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_splitSubexpProfile_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_splitSubexpProfile hlim hdecay hprofile

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_splitSubexpProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_splitSubexpProfile_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_splitSubexpProfile hlim hdecay hprofile

/--
[freePosSubcriticalMassBridge_of_boundaryVertexPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boundaryVertexPointwise_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_boundaryVertexPointwise hlim hfixed hprofile

/--
[freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_profileSubexpComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_profilePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_profilePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_profilePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_profileFiniteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_profileFiniteVolumeComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_profileFiniteVolumeComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_profileFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_vertexDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_vertexDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_vertexDoubleScale hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_profileDoubleScale hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxPolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxPolynomialProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalMassBridge_of_simonFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_simonFreeSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_simonFreeSum_projection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_simonFreeSum_doubledBoxProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep hlim hfixed hsimon hstep

/--
[freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches hlim hfixed hsimon hstrict hdiag

/--
[freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_projection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep hlim hfixed hfinite hstep

/--
[freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches hlim hfixed hfinite hstrict hdiag

/--
[freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalMassBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale hlim hfixed hsimon hstrict hdiag hprofile

/--
[freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale hlim hfixed hfinite hstrict hdiag hprofile

/--
[freePosSubcriticalMassBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale hlim hfixed hSimon hstrict hdiag hprofile

/--
[freePosSubcriticalMassBridge_of_finiteIsingSimon_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteIsingSimon_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteIsingSimon_projection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep hlim hfixed hSimon hstep

/--
[freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches hlim hfixed hSimon hstrict hdiag

/--
[freePosSubcriticalMassBridge_of_subexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_subexpComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_subexpComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_polynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_polynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_polynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_finiteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteVolumeComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteVolumeComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_finiteVolumePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalMassBridge_of_envelopeAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_envelopeAtLeastMass_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (henv : FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_envelopeAtLeastMass hlim hfixed henv

/--
[freePosSubcriticalMassBridge_of_polynomialAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_polynomialAtLeastMass_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hpoly : FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_polynomialAtLeastMass hlim hfixed hpoly

/--
[freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_polynomialRateWithXAxisLogRate hlim hfixed hrate

/--
[freePosSubcriticalMassBridge_of_directionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_directionalRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_directionalRate hlim hfixed hdir

/--
[freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_convexSurfaceTensionUpper hlim hfixed htension

/--
[freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_actualConvexSurfaceTensionUpper hlim hfixed htension

/--
[freePosSubcriticalCorrBridge_of_boundaryVertexPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_boundaryVertexPointwise_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_boundaryVertexPointwise hlim hfixed hprofile

/--
[freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_profileSubexpComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_profilePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_profilePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_profilePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_profileFiniteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_profileFiniteVolumeComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_profileFiniteVolumeComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_profileFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_profileScaledFiniteVolumePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_vertexDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_vertexDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_vertexDoubleScale hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_profileDoubleScale hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_simonFreeSum_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_simonFreeSum_doubledBoxPolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_simonFreeSum_doubledBoxPolynomialProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgePolynomialProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalCorrBridge_of_simonFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_simonFreeSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_simonFreeSum_projection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalCorrBridge_of_simonFreeSum_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_simonFreeSum_doubledBoxProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_simonFreeSum_doubledBoxProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeProjection hlim hfixed hsimon hprojection

/--
[freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStep hlim hfixed hsimon hstep

/--
[freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_simonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches hlim hfixed hsimon hstrict hdiag

/--
[freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_projection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_doubledBoxProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_doubledBoxProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeProjection hlim hfixed hfinite hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStep hlim hfixed hfinite hstep

/--
[freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches hlim hfixed hfinite hstrict hdiag

/--
[freePosSubcriticalCorrBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalCorrBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_simonFreeSum_fullCoordinateComparisons_profileDoubleScale hlim hfixed hsimon hstrict hdiag hprofile

/--
[freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale hlim hfixed hfinite hstrict hdiag hprofile

/--
[freePosSubcriticalCorrBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale hlim hfixed hSimon hstrict hdiag hprofile

/--
[freePosSubcriticalCorrBridge_of_finiteIsingSimon_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteIsingSimon_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteIsingSimon_projection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteIsingSimon_doubledBoxProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteIsingSimon_doubledBoxProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteIsingSimon_doubledBoxProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeProjection hlim hfixed hSimon hprojection

/--
[freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstep : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeCoordinateStepDoubledBoxProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStep hlim hfixed hSimon hstep

/--
[freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches hlim hfixed hSimon hstrict hdiag

/--
[freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_subexpComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_polynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_polynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexPolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_polynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_finiteVolumeComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteVolumeComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumeComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteVolumeComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_finiteVolumePolynomialComparisonToXAxis hlim hfixed hcompare

/--
[freePosSubcriticalCorrBridge_of_envelopeAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_envelopeAtLeastMass_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (henv : FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_envelopeAtLeastMass hlim hfixed henv

/--
[freePosSubcriticalCorrBridge_of_polynomialAtLeastMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_polynomialAtLeastMass_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hpoly : FreeQ2BoundaryVertexPolynomialAtLeastMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_polynomialAtLeastMass hlim hfixed hpoly

/--
[freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_polynomialRateWithXAxisLogRate hlim hfixed hrate

/--
[freePosSubcriticalCorrBridge_of_directionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_directionalRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_directionalRate hlim hfixed hdir

/--
[freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_convexSurfaceTensionUpper hlim hfixed htension

/--
[freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_actualConvexSurfaceTensionUpper hlim hfixed htension

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_boundaryPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_boundaryPointwise_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_boundaryPointwise hlim hdecay hprofile

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_subexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_subexpComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_subexpComparisonToXAxis hlim hdecay hcompare

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_boundaryPointwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_boundaryPointwise_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_boundaryPointwise hlim hdecay hprofile

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_subexpComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_subexpComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexSubexpComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_subexpComparisonToXAxis hlim hdecay hcompare

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis hlim hdecay hcompare

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis hlim hdecay hcompare

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate hlim hdecay hrate

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_directionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_directionalRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_directionalRate hlim hdecay hdir

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper hlim hdecay htension

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper hlim hdecay htension

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hrate : FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate hlim hdecay hrate

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_directionalRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_directionalRate_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hdir : FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_directionalRate hlim hdecay hdir

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper hlim hdecay htension

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper hlim hdecay htension

/--
[freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate_eq
-- given
  (h : FreeQ2ProfileSeparatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeQ2ProfileSeparate h

/--
[plusPosSubcriticalMassBridge_of_freeQ2ProfileSeparate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeQ2ProfileSeparate_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreeQ2ProfileSeparatePositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeQ2ProfileSeparate hagree h

/--
[freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_eq
-- given
  (h : FreeQ2ProfileSeparatePositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeQ2ProfileSeparate h

/--
[plusPosSubcriticalCorrBridge_of_freeQ2ProfileSeparate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeQ2ProfileSeparate_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (h : FreeQ2ProfileSeparatePositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeQ2ProfileSeparate hagree h

/--
[freePosSubcriticalMassBridge_of_freeFVQ2Exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2Exact_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2Exact hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_freeFVQ2Exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeFVQ2Exact_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeFVQ2Exact hagree hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_freeFVQ2Subexp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2Subexp_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2Subexp hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_freeFVQ2Subexp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeFVQ2Subexp hagree hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided hagree hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_wiredFVQ2Exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_wiredFVQ2Exact_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_wiredFVQ2Exact hbad hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_wiredFVQ2Exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_wiredFVQ2Exact_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_wiredFVQ2Exact hagree hbad hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_wiredFVQ2Subexp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_wiredFVQ2Subexp hbad hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp hagree hbad hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided hagree hbad hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeFVQ2Exact_belowBetaC hagree hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_belowBetaC hagree hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_belowBetaC hagree hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison hagree hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison hagree hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison hagree hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC hbad hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_wiredFVQ2Exact_belowBetaC hagree hbad hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC hbad hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_wiredFVQ2Subexp_belowBetaC hagree hbad hcmp hdecay

/--
[freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.freePosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay

/--
[plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.plusPosSubcriticalMassBridge_of_wiredFVQ2TwoSided_belowBetaC hagree hbad hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2Exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2Exact_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2Exact hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_freeFVQ2Exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeFVQ2Exact_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeFVQ2Exact hagree hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2Subexp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2Subexp hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp hagree hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided hagree hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_wiredFVQ2Exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_wiredFVQ2Exact hbad hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_wiredFVQ2Exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_wiredFVQ2Exact_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_wiredFVQ2Exact hagree hbad hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp hbad hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_wiredFVQ2Subexp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_wiredFVQ2Subexp_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_wiredFVQ2Subexp hagree hbad hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided hbad hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_wiredFVQ2TwoSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparison)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_wiredFVQ2TwoSided hagree hbad hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeFVQ2Exact_belowBetaC hagree hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp_belowBetaC hagree hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided_belowBetaC hagree hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeFVQ2Exact_restrictedCylinderComparison hagree hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeFVQ2Subexp_restrictedCylinderComparison hagree hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison_eq
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison hagree hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2ExactPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC hbad hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2ExactPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_wiredFVQ2Exact_belowBetaC hagree hbad hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC hbad hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2SubexpPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_wiredFVQ2Subexp_belowBetaC hagree hbad hcmp hdecay

/--
[freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC_eq
-- given
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.freePosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC hbad hcmp hdecay

/--
[plusPosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean)
-/
@[path]
private lemma plusPosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC_eq
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbad : Q2PositiveSubcriticalNotBad)
  (hcmp : FreeQ2PositiveSubcriticalComparisonBelowBetaC)
  (hdecay : WiredFVQ2TwoSidedPositiveSubcritical) :
-- imply
  PlusPositiveSubcriticalCorrelationLengthBridge := by
-- proof
  apply StatMech.plusPosSubcriticalCorrBridge_of_wiredFVQ2TwoSided_belowBetaC hagree hbad hcmp hdecay


-- created on 2026-10-23
