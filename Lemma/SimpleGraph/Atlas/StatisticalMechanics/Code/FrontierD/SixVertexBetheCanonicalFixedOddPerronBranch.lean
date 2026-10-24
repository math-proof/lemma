import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch
open Filter Topology StatMech StatMech.FrontierD


/--
[eventually_exists_sixVertexFixedOddChargeBethePerronBranch_with_densityFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOddPerronBranch.lean)
-/
@[path]
private lemma eventually_exists_sixVertexFixedOddChargeBethePerronBranch_with_densityFloor_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∃ lower : Real, 0 < lower ∧ ∀ᶠ k : Nat in atTop, ∃ p, SixVertexFixedOddChargePerronBranchWitness c s k p ∧ ∀ x, lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) p x := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexFixedOddChargeBethePerronBranch_with_densityFloor hc s

/--
[eventually_exists_sixVertexFixedOddChargeBethePerronBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOddPerronBranch.lean)
-/
@[path]
private lemma eventually_exists_sixVertexFixedOddChargeBethePerronBranch_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, ∃ p, SixVertexFixedOddChargePerronBranchWitness c s k p := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexFixedOddChargeBethePerronBranch hc s

/--
[eventually_sixVertexCanonicalFixedOddChargePerronBetheRoots_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOddPerronBranch.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedOddChargePerronBetheRoots_witness_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, SixVertexFixedOddChargePerronBranchWitness c s k (sixVertexCanonicalFixedOddChargePerronBetheRoots hc s k) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedOddChargePerronBetheRoots_witness hc s

/--
[eventually_sixVertexCanonicalFixedOddChargeBetheEigenvalueValue_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOddPerronBranch.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedOddChargeBetheEigenvalueValue_eq_top_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc s k = sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (by unfold sixVertexFourWidth omega) c := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedOddChargeBetheEigenvalueValue_eq_top hc s


-- created on 2026-10-23
