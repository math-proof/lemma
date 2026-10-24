import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexCorrectedStripInfiniteIdentity
open StatMech StatMech.Universality


/--
[hexCSInfiniteSideMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripInfiniteIdentity.lean)
-/
@[path]
private lemma hexCSInfiniteSideMass_nonneg_eq
  {v : ℕ} :
-- imply
  0 ≤ hexCSInfiniteSideMass v := by
-- proof
  apply StatMech.Universality.hexCSInfiniteSideMass_nonneg v

/--
[hexCSInfiniteTopMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripInfiniteIdentity.lean)
-/
@[path]
private lemma hexCSInfiniteTopMass_nonneg_eq
  {v : ℕ} :
-- imply
  0 ≤ hexCSInfiniteTopMass v := by
-- proof
  apply StatMech.Universality.hexCSInfiniteTopMass_nonneg v

/--
[hexCSPredicateWeight_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripInfiniteIdentity.lean)
-/
@[path]
private lemma hexCSPredicateWeight_summable_eq
-- given
  (P : List ℤ → Prop)
  (hlegal : ∀ ts, P ts → (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  Summable (hexCSPredicateWeight P) := by
-- proof
  apply StatMech.Universality.hexCSPredicateWeight_summable P hlegal hwalk

/--
[hexCSPredicateMass_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripInfiniteIdentity.lean)
-/
@[path]
private lemma hexCSPredicateMass_mono_eq
-- given
  (P Q : List ℤ → Prop)
  (hPQ : ∀ ts, P ts → Q ts)
  (hlegalQ : ∀ ts, Q ts → (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  hexCSPredicateMass P ≤ hexCSPredicateMass Q := by
-- proof
  apply StatMech.Universality.hexCSPredicateMass_mono P Q hPQ hlegalQ hwalk

/--
[hexCSInfiniteSideMass_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripInfiniteIdentity.lean)
-/
@[path]
private lemma hexCSInfiniteSideMass_mono_eq
  {v : ℕ}
-- given
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  hexCSInfiniteSideMass v ≤ hexCSInfiniteSideMass (v + 1) := by
-- proof
  apply StatMech.Universality.hexCSInfiniteSideMass_mono hwalk v

/--
[hexCS_infinite_height_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripInfiniteIdentity.lean)
-/
@[path]
private lemma hexCS_infinite_height_identity_eq
  {v : ℕ}
-- given
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
  (hlocal : ∀ L, HexCSLocalRelation (v + 1) L (Nat.succ_pos v))
  (hwindow : ∀ L, HexCSBoundaryWindowLaw (v + 1) L (Nat.succ_pos v)) :
-- imply
  hexCl * hexCSInfiniteSideMass v + hexCSInfiniteTopMass v = 1 := by
-- proof
  apply StatMech.Universality.hexCS_infinite_height_identity v hwalk hlocal hwindow


-- created on 2026-10-23
