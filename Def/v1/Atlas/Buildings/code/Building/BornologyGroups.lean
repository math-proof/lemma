/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.ApplicationsToGroups.Part4
import Lemma.Nat.TopologicalGroupDef
import Mathlib.Topology.Bornology.Basic
set_option linter.unusedSectionVars false

open Set Filter Classical


/-- Set-theoretic product $EF = \{ ef : e \in E, f \in F \}$ in a multiplicative structure. -/
def GroupSetMul {G : Type*} [Mul G] (E F : Set G) : Set G :=
  {g | ∃ e ∈ E, ∃ f ∈ F, g = e * f}

/-- Set-theoretic inverse $E^{-1} = \{e^{-1} : e \in E\}$. -/
def GroupSetInv {G : Type*} [Inv G] (E : Set G) : Set G :=
  {g | ∃ e ∈ E, g = e⁻¹}

