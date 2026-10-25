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
import Def.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.IsCoxeterCharacterized
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace ChamberComplex

/-- $K$ is *Coxeter-characterized*: it is thin and every adjacent pair has a folding that
separates them (one fixed, one moved). -/
structure IsCoxeterCharacterized (K : ChamberComplex V) : Prop where
  thin : K.IsThin
  wallSeparation : ∀ C D, K.toSimplicialComplex.Adjacent C D →
    ∃ f : Folding K,
      (C.image f.morph.toFun = C ∧ D.image f.morph.toFun ≠ D) ∨
      (D.image f.morph.toFun = D ∧ C.image f.morph.toFun ≠ C)

end ChamberComplex
