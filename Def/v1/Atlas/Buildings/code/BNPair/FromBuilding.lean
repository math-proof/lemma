/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/FromBuilding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Lemma.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
import Def.v1.Atlas.Buildings.code.Building.Labels
import Def.v1.Atlas.Buildings.code.Building.RetractionDef
import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
import Structure.v1.Atlas.Buildings.code.BNPair.FromBuilding
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


namespace Building

namespace GroupAction

variable {G : Type*} [Group G] {b : Building V} (act : GroupAction G b)

/-- The action of $g \in G$ on a finite face $s$: the image of $s$ under $v \mapsto g \cdot v$. -/
def smulFace (g : G) (s : Finset V) : Finset V :=
  s.image (act.smul g)

/-- The action of $g \in G$ on a set of faces $F$: image of $F$ under `smulFace g`. -/
def smulFaces (g : G) (F : Set (Finset V)) : Set (Finset V) :=
  { s | ∃ t ∈ F, s = act.smulFace g t }

end GroupAction
end Building
