/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/FixedPointSubgroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.BruhatTitsFixedPoint
import Lemma.Set.RadiusFrom.ge.Zero
import Lemma.Set.BNPairBoundedPredicate_SetMul.of.BNPairBoundedPredicate.BNPairBoundedPredicate
import sympy.atlas.v1.Atlas.Buildings.code.Building.CompactSubgroups
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.Generalized.Defs

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

open Set

/-- Restrict an isometric action of $G$ on $X$ to an action of a subgroup
$K \leq G$. -/
def restrictIsometricAction {G : Type*} [Group G] {X : Type*} [MetricSpace X]
    (act : IsometricAction G X) (K : Subgroup G) : IsometricAction K X where
  smul := fun ⟨g, _⟩ x => act.smul g x
  smul_one := by
    intro x; show act.smul (1 : G) x = x; exact act.smul_one x
  smul_mul := by
    intro ⟨g, _⟩ ⟨h, _⟩ x
    show act.smul (g * h) x = act.smul g (act.smul h x)
    exact act.smul_mul g h x
  isometry_smul := by
    intro ⟨g, _⟩; exact act.isometry_smul g

namespace FixedPointSubgroups

variable {Gt : Type*} [Group Gt] {X : Type*} [MetricSpace X]

/-- The orbit $E \cdot x = \{g \cdot x \mid g \in E\}$ of a point $x$ under
a subset $E$ of the group. -/
def orbitSet (act : IsometricAction Gt X)
    (E : Set Gt) (x : X) : Set X :=
  { y : X | ∃ g ∈ E, act.smul g x = y }

/-- The image $E \cdot Y = \{g \cdot y \mid g \in E,\, y \in Y\}$ of a
subset $Y \subseteq X$ under a subset $E$ of the group. -/
def actionOnSet (act : IsometricAction Gt X)
    (E : Set Gt) (Y : Set X) : Set X :=
  { z : X | ∃ g ∈ E, ∃ y ∈ Y, act.smul g y = z }

/-- The stabilizer subgroup $\mathrm{Stab}(x) = \{g \in G \mid g \cdot x = x\}$
of a point $x \in X$. -/
def pointStabilizer (act : IsometricAction Gt X)
    (x : X) : Subgroup Gt where
  carrier := { g : Gt | act.smul g x = x }
  mul_mem' := by
    intro a b ha hb
    show act.smul (a * b) x = x
    rw [act.smul_mul, hb, ha]
  one_mem' := act.smul_one x
  inv_mem' := by
    intro a ha
    show act.smul a⁻¹ x = x
    have h1 : act.smul a⁻¹ (act.smul a x) = act.smul (a⁻¹ * a) x :=
      (act.smul_mul a⁻¹ a x).symm
    rw [inv_mul_cancel] at h1
    rw [act.smul_one] at h1
    rw [ha] at h1
    exact h1

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

attribute [instance] BuildingGroupContext.metricSpace BuildingGroupContext.completeSpace
  BuildingGroupContext.nonempty
