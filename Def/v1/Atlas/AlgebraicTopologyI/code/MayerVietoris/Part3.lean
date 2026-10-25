/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.MayerVietoris
open Set Topology EilenbergSteenrod Function

universe u


namespace MayerVietoris

attribute [instance] MayerVietorisCover.instTop

/-- The homeomorphism of pairs from the sub-pair of `EP` to `(A ∩ B, ∅)`: each point of
the excised subspace lies in `A` (by sub-pair membership) and in `B` (since it is not
in `Bᶜ`). -/
def MayerVietorisCover.trSub (c : MayerVietorisCover) : MapOfPairs c.EP.subPair c.pairAB where
  toFun := fun p => ⟨p.1.1, ⟨p.2, not_not.mp p.1.2⟩⟩
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  mapsTo := fun _ h => h.elim

/-- Inverse to `trSub`: each point of `A ∩ B` lies outside `Bᶜ`, hence in the sub-pair
of the excised pair `EP`. -/
def MayerVietorisCover.trSubInv (c : MayerVietorisCover) : MapOfPairs c.pairAB c.EP.subPair where
  toFun := fun p => ⟨⟨p.1, not_not.mpr p.2.2⟩, p.2.1⟩
  continuous_toFun := (Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _)
  mapsTo := fun _ h => h.elim

/-- The homeomorphism of pairs from the total-space pair of `EP` to `(B, ∅)`: a point
of `X` that lies outside `Bᶜ` is the same data as a point of `B`. -/
def MayerVietorisCover.trSp (c : MayerVietorisCover) :
    MapOfPairs (TopPair.ofSpace c.EP.space) c.pairB where
  toFun := fun p => ⟨p.1, not_not.mp p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun _ h => h.elim

/-- Inverse to `trSp`: a point of `B` corresponds to the point of `X` lying outside
`Bᶜ` in the total space of the excised pair. -/
def MayerVietorisCover.trSpInv (c : MayerVietorisCover) :
    MapOfPairs c.pairB (TopPair.ofSpace c.EP.space) where
  toFun := fun p => ⟨p.1, not_not.mpr p.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun _ h => h.elim

/-- The constant homotopy from a self-map of a pair `f : P → P` that acts as the
identity on points (`f x = x`) to the identity map of `P`. -/
def constHomotopy {P : TopPair} (f : MapOfPairs P P) (hf : ∀ x, f.toFun x = x) :
    HomotopyOfPairMaps f (MapOfPairs.id P) where
  toFun := fun ⟨x, _⟩ => x
  continuous_toFun := continuous_fst
  map_zero := fun x => (hf x).symm
  map_one := fun _ => rfl
  mapsTo := fun _ ha _ => ha

end MayerVietoris
