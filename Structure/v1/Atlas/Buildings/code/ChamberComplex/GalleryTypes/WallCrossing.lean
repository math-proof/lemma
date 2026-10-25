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
import Def.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.WallCrossing
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace ChamberComplex

/-- *Wall-crossing properties*: in a minimal gallery, two same-side endpoints give no wall
crossings, opposite-side endpoints give at least one wall crossing, and minimal galleries cross
each wall at most once. -/
structure WallCrossingProperties (K : ChamberComplex V) where
  both_fixed_no_crossing :
    ∀ (f : Folding K) (C D : Finset V),
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal D →
      C.image f.morph.toFun = C →
      D.image f.morph.toFun = D →
      ∀ (g : Gallery K.toSimplicialComplex),
        g.Connects C D →
        g.length = galleryDist K.toSimplicialComplex C D →
        g.WallCrossings f = ∅
  both_moved_no_crossing :
    ∀ (f : Folding K) (C D : Finset V),
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal D →
      C.image f.morph.toFun ≠ C →
      D.image f.morph.toFun ≠ D →
      ∀ (g : Gallery K.toSimplicialComplex),
        g.Connects C D →
        g.length = galleryDist K.toSimplicialComplex C D →
        g.WallCrossings f = ∅
  opposite_at_least_one :
    ∀ (f : Folding K) (C D : Finset V),
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal D →
      OppositeSides f C D →
      ∀ (g : Gallery K.toSimplicialComplex),
        g.Connects C D →
        ∃ i, i ∈ g.WallCrossings f
  at_most_one_crossing :
    ∀ (f : Folding K) (C D : Finset V),
      K.toSimplicialComplex.IsMaximal C →
      K.toSimplicialComplex.IsMaximal D →
      ∀ (g : Gallery K.toSimplicialComplex),
        g.Connects C D →
        g.length = galleryDist K.toSimplicialComplex C D →
        ∀ i j : Fin (g.chambers.length - 1),
          i ∈ g.WallCrossings f →
          j ∈ g.WallCrossings f →
          i = j

end ChamberComplex
