/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/IsCoxeterCharacterized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
import Lemma.List.All.of.All.IsChain.Ne
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Def.v1.Atlas.Buildings.code.Building.Labels
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace Gallery

/-- A gallery is *non-stuttering* if consecutive chambers are always distinct. -/
def IsNonStuttering {K : SimplicialComplex V} (g : Gallery K) : Prop :=
  ∀ i : Fin (g.chambers.length - 1),
    g.chambers[i.val] ≠ g.chambers[i.val + 1]

end Gallery

/-- The *type* of a gallery under a labelling: the list of label-sets of the shared codim-$1$
faces along consecutive chambers. -/
def GalleryType {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L)
    (g : Gallery K.toSimplicialComplex) : List (Finset L) :=
  (List.zip g.chambers g.chambers.tail).map
    fun p => lab.labelMap (p.1 ∩ p.2)

