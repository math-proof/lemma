/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/AffineFunc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Infinity.Sectors.Part3
import Lemma.Fin.All_All_Any_And_InAndAll_In_Vertices
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- $f$ is bounded above on the set $S$: $∃ c, ∀ z ∈ S, f(z) ≤ c$. -/
def BoundedAboveOn (f : V → ℝ) (S : Set V) : Prop :=
  ∃ c : ℝ, ∀ z ∈ S, f z ≤ c

/-- $f$ is bounded below on $S$: $∃ c, ∀ z ∈ S, c ≤ f(z)$. -/
def BoundedBelowOn (f : V → ℝ) (S : Set V) : Prop :=
  ∃ c : ℝ, ∀ z ∈ S, c ≤ f z

end AffineBuilding
