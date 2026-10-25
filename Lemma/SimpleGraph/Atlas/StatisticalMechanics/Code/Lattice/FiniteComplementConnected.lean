import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
open Set SimpleGraph StatMech StatMech.Lattice


/--
[fcc_xLowerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FiniteComplementConnected.lean)
-/
@[path]
private lemma fcc_xLowerBound_eq
  {F : Set (Site 2)}
-- given
  (hF : F.Finite) :
-- imply
  ∃ b : ℤ, ∀ q ∈ F, b ≤ q 0 := by
-- proof
  apply StatMech.Lattice.fcc_xLowerBound F hF

/--
[fcc_horizWalk_off_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FiniteComplementConnected.lean)
-/
@[path]
private lemma fcc_horizWalk_off_finite_eq
  {F : Set (Site 2)}
  {b : ℤ}
  {z : Site 2}
  {M : ℤ}
-- given
  (hb : ∀ q ∈ F, b ≤ q 0)
  (hz : z 0 < b)
  (hM : M ≤ z 0) :
-- imply
  ∀ w ∈ (sw_horizSeg (z 1) (z 0) M).support, w ∉ F := by
-- proof
  apply StatMech.Lattice.fcc_horizWalk_off_finite F b hb z hz M hM

/--
[fcc_far_reach_off_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FiniteComplementConnected.lean)
-/
@[path]
private lemma fcc_far_reach_off_finite_eq
  {F : Set (Site 2)}
-- given
  (hF : F.Finite) :
-- imply
  ∃ b : ℤ, (∀ q ∈ F, b ≤ q 0) ∧ ∀ z : Site 2, z 0 ≤ b - 1 → ∀ M : ℤ, M ≤ z 0 → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ F) ∧ (∀ q ∈ F, z0 0 ≤ q 0) ∧ z0 = ![M, z 1] := by
-- proof
  apply StatMech.Lattice.fcc_far_reach_off_finite F hF


-- created on 2026-10-23
