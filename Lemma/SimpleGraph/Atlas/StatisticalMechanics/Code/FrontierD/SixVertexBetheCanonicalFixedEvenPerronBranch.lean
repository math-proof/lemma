import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
open Filter Topology StatMech StatMech.FrontierD


/--
[exists_uniform_sixVertexFixedChargeDensityGaugeNumericalMargins_Ici](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean)
-/
@[path]
private lemma exists_uniform_sixVertexFixedChargeDensityGaugeNumericalMargins_Ici_eq
  {a rhoLower : Real}
  {r : Nat}
-- given
  (ha : 2 < a)
  (hrhoLower : 0 < rhoLower) :
-- imply
  ∃ inner outer : Real, 0 < outer ∧ inner < outer ∧ (∀ c, a ≤ c → outer ≤ rhoLower * ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) / 2) ∧ ∀ᶠ N : Nat in atTop, ∀ c, a ≤ c → sixVertexRootDensityContractionRate c * outer + sixVertexFixedChargeDensityStabilityErrorOfLower c N r (rhoLower / 2) ≤ inner ∧ sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) < 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.exists_uniform_sixVertexFixedChargeDensityGaugeNumericalMargins_Ici ha hrhoLower r

/--
[sixVertexCanonicalFixedEvenChargeContinuationPoint_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedEvenChargeContinuationPoint_projection_eq
  {a b c : Real}
  {s k : Nat}
-- given
  (ha : 2 < a)
  (hc : c ∈ Set.Icc a b) :
-- imply
  sixVertexBetheContinuationProjection (sixVertexCanonicalFixedEvenChargeContinuationPoint ha hc s k) = ⟨c, hc⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedEvenChargeContinuationPoint_projection ha hc s k

/--
[eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean)
-/
@[path]
private lemma eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∃ lower : Real, 0 < lower ∧ ∀ᶠ k : Nat in atTop, ∃ p, SixVertexFixedEvenChargePerronBranchWitness c s k p ∧ ∀ x, lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) p x := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor hc s

/--
[eventually_exists_sixVertexFixedEvenChargeBethePerronBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean)
-/
@[path]
private lemma eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, ∃ p, SixVertexFixedEvenChargePerronBranchWitness c s k p := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexFixedEvenChargeBethePerronBranch hc s

/--
[eventually_sixVertexCanonicalFixedEvenChargePerronBetheRoots_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedEvenChargePerronBetheRoots_witness_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, SixVertexFixedEvenChargePerronBranchWitness c s k (sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedEvenChargePerronBetheRoots_witness hc s

/--
[eventually_sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue_eq_top_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc s k = sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (by unfold sixVertexFourWidth omega) c := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue_eq_top hc s


-- created on 2026-10-23
