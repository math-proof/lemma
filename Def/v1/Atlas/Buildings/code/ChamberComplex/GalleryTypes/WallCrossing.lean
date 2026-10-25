/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/WallCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
import Lemma.List.All.of.All.IsChain.Ne
import Lemma.List.Any.of.Not.In_A.IsChainA
import Def.v1.Atlas.Buildings.code.Building.Convexity
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace Gallery

/-- The gallery $g$ *crosses the wall of $f$* at edge $i$ if $g_i$ and $g_{i+1}$ lie on opposite
sides of the wall. -/
def CrossesWallAt {K : ChamberComplex V}
    (g : Gallery K.toSimplicialComplex) (f : ChamberComplex.Folding K)
    (i : Fin (g.chambers.length - 1)) : Prop :=
  ChamberComplex.OppositeSides f g.chambers[i.val] g.chambers[i.val + 1]

/-- The set of edges along $g$ at which the gallery crosses the wall of $f$. -/
def WallCrossings {K : ChamberComplex V}
    (g : Gallery K.toSimplicialComplex) (f : ChamberComplex.Folding K) :
    Set (Fin (g.chambers.length - 1)) :=
  { i | g.CrossesWallAt f i }

end Gallery
