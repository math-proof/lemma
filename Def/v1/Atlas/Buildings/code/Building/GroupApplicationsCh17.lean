/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.ApplicationsToGroups.Part4
import Lemma.Nat.TopologicalGroupDef
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Group
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Topology Filter


section Conjugation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation by $g$ as a self-homeomorphism of a topological group $G$. -/
def conjHomeomorph (g : G) : G ≃ₜ G where
  toEquiv := MulAut.conj g
  continuous_toFun := by
    show Continuous (fun x => g * x * g⁻¹)
    exact (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := by
    show Continuous (fun x => g⁻¹ * x * g)
    exact (continuous_const.mul continuous_id).mul continuous_const

/-- The conjugate $gSg^{-1}$ of a subset $S \subseteq G$. -/
def conjSet (g : G) (S : Set G) : Set G :=
  (conjHomeomorph g) '' S

/-- The pointwise fixer of a subset $Y \subseteq X$ under a group action:
the set of group elements that fix every point of $Y$. -/
def pointwiseFixer {G : Type*} {X : Type*} (act : G → X → X) (Y : Set X) : Set G :=
  {g : G | ∀ y ∈ Y, act g y = y}

end Conjugation
