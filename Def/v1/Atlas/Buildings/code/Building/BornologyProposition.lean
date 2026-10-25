/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyProposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.BornologyGroups.Part3
import Lemma.Set.Empty.in.Bounded
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
set_option linter.unusedSectionVars false

open Set


namespace BornologyProp

variable {G : Type*} {X : Type*}

/-- Orbit of a point $x$ under the action of a set $E \subseteq G$: $\{g \cdot x : g \in E\}$. -/
def pointOrbit (act : G → X → X) (E : Set G) (x : X) : Set X :=
  {z | ∃ g ∈ E, z = act g x}

/-- Orbit of a set $Y \subseteq X$ under the action of $E \subseteq G$: $\{g \cdot y : g \in E, y \in Y\}$. -/
def setOrbit (act : G → X → X) (E : Set G) (Y : Set X) : Set X :=
  {z | ∃ g ∈ E, ∃ y ∈ Y, z = act g y}

end BornologyProp
