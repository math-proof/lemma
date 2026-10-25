/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.BruhatTitsFixedPoint.Part2
import Lemma.Set.RadiusFrom.ge.Zero
import Lemma.Set.BNPairBoundedPredicate_SetMul.of.BNPairBoundedPredicate.BNPairBoundedPredicate
import Structure.v1.Atlas.Buildings.code.Building.CompactSubgroups.Part2
import Structure.v1.Atlas.Buildings.code.BNPair.Generalized.Defs
import Def.v1.Atlas.Buildings.code.Building.FixedPointSubgroups
set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


noncomputable section

open Set

namespace FixedPointSubgroups

variable {Gt : Type*} [Group Gt] {X : Type*} [MetricSpace X]

/-- A package of data and axioms needed to relate bounded subgroups of a
group $G^t$ acting on a $\mathrm{CAT}(0)$ space $X$ to point stabilizers:
an isometric action satisfying the negative-curvature inequality, a
generalised BN-pair, a group bornology, a base chamber point, and
compatibility axioms ensuring boundedness is equivalent to having a bounded
orbit. -/
structure BuildingGroupContext (Gt : Type*) [Group Gt] (B_idx : Type*)
    (M : CoxeterMatrix B_idx) where
  X : Type*
  [metricSpace : MetricSpace X]
  [completeSpace : CompleteSpace X]
  [nonempty : Nonempty X]
  nci : NegativeCurvatureInequality X
  action : IsometricAction Gt X
  gbnpair : GeneralizedBNPair Gt M
  bruhatProps : BNPair.BruhatProperties gbnpair.strictBNPair
  born : CompactSubgroups.GroupBornology Gt
  chamber_point : X
  borel_fixes_chamber_point :
    ∀ (b : Gt), b ∈ gbnpair.strictBNPair.B.map gbnpair.G.subtype →
      action.smul b chamber_point = chamber_point
  Tt_fixes_chamber_point :
    ∀ (t : Gt), t ∈ gbnpair.Tt → action.smul t chamber_point = chamber_point
  born_bounded_orbit_at_chamber_point :
    ∀ (E : Set Gt), born.isBounded E →
      Bornology.IsBounded (orbitSet action E chamber_point)
  orbit_bounded_at_chamber_point_born_bounded :
    ∀ (E : Set Gt), Bornology.IsBounded (orbitSet action E chamber_point) →
      born.isBounded E
  Tt_in_every_maximal_bounded :
    ∀ (K : Subgroup Gt), CompactSubgroups.IsMaximalBounded born K →
      ∀ (t : Gt), t ∈ gbnpair.Tt → t ∈ K
  stabilizer_of_bounded_orbit :
    ∀ (x : X) (H : Subgroup Gt),
      pointStabilizer action x ≤ H →
      Bornology.IsBounded (orbitSet action (H : Set Gt) x) →
      H ≤ pointStabilizer action x

end FixedPointSubgroups
end
