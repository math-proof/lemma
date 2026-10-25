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

end FixedPointSubgroups
end
