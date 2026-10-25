/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/SectorParallelism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Infinity.AffineFunc.Part2
import Lemma.Set.Functional.ge.Zero
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Two sectors are *parallel* if they share a common subsector $T$ with
$T \subseteq S_1$ and $T \subseteq S_2$ (Section 16.6). -/
def Sector.Parallel (b : Building V) (S₁ S₂ : Sector b) : Prop :=
  ∃ (T : Sector b), Sector.Subsector b T S₁ ∧ Sector.Subsector b T S₂

end AffineBuilding
