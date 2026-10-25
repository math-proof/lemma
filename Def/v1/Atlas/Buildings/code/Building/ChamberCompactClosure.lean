/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ChamberCompactClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Compactness.Compact
set_option linter.unusedSectionVars false

open Classical


/-- The group action $W \to E \to E$ acts by isometries iff every element $w \in W$ acts as an
isometry of the metric space $E$. -/
def ActsByIsometries : Prop :=
  ∀ w : W, Isometry (action w)

/-- The image $w \cdot S$ of a subset $S \subseteq E$ under the action of $w \in W$. -/
def orbitSet (w : W) (S : Set E) : Set E :=
  action w '' S

