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
import Structure.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.IsCoxeterCharacterized
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace ChamberComplex

/-- The *type-deletion condition* for galleries: any non-minimal non-stuttering gallery admits a
shorter gallery whose type is obtained by deleting two letters at positions $i < j$ from the
original type, mirroring the Coxeter deletion condition. -/
def HasTypeDeletion {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L) : Prop :=
  ∀ (g : Gallery K.toSimplicialComplex) (C D : Finset V),
    g.IsNonStuttering →
    g.Connects C D →
    g.length > galleryDist K.toSimplicialComplex C D →
    ∃ (g' : Gallery K.toSimplicialComplex),
      g'.Connects C D ∧
      g'.length < g.length ∧
      ∃ (i j : ℕ), i < j ∧ j < (GalleryType K lab g).length ∧
        GalleryType K lab g' =
          (GalleryType K lab g).take i ++
          ((GalleryType K lab g).drop (i + 1)).take (j - i - 1) ++
          (GalleryType K lab g).drop (j + 1)

end ChamberComplex
