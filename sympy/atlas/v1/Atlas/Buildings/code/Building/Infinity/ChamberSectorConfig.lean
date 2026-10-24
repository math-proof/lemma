/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/ChamberSectorConfig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Infinity.Sectors
import Lemma.Fin.All_All_Any_And_InAndAll_In_Vertices
import Lemma.Finset.AgreeOnImage.of.AgreeOn
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.Uniqueness

set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- Predicate: $v$ is a vertex of $K$ (lies in some face). -/
def IsVertexOf (K : SimplicialComplex V) (v : V) : Prop :=
  ∃ s ∈ K.faces, v ∈ s

end AffineBuilding
