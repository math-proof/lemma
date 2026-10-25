/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Structure.v1.Atlas.AlgebraicTopologyI.code.MayerVietoris
open Set Topology EilenbergSteenrod Function

universe u


namespace MayerVietoris

attribute [instance] MayerVietorisCover.instTop

/-- The trivial pair `(X, ∅)` associated to the ambient space of a Mayer-Vietoris cover. -/
def MayerVietorisCover.pairX (c : MayerVietorisCover) : TopPair := TopPair.ofSpace c.X

/-- The trivial pair `(A, ∅)` associated to the first cover element. -/
def MayerVietorisCover.pairA (c : MayerVietorisCover) : TopPair := TopPair.ofSpace c.A

/-- The trivial pair `(B, ∅)` associated to the second cover element. -/
def MayerVietorisCover.pairB (c : MayerVietorisCover) : TopPair := TopPair.ofSpace c.B

/-- The trivial pair `(A ∩ B, ∅)` associated to the intersection of the cover elements. -/
def MayerVietorisCover.pairAB (c : MayerVietorisCover) : TopPair :=
  TopPair.ofSpace (c.A ∩ c.B : Set c.X)

/-- The inclusion of pairs `(A ∩ B, ∅) ↪ (A, ∅)`, which underlies the map
`j_1 : H_n(A ∩ B) → H_n(A)` in the Mayer-Vietoris sequence. -/
def MayerVietorisCover.inclAB_A (c : MayerVietorisCover) : MapOfPairs c.pairAB c.pairA where
  toFun := fun x => ⟨x.1, x.2.1⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun _ h => h.elim

/-- The inclusion of pairs `(A ∩ B, ∅) ↪ (B, ∅)`, which underlies the map
`j_2 : H_n(A ∩ B) → H_n(B)` in the Mayer-Vietoris sequence. -/
def MayerVietorisCover.inclAB_B (c : MayerVietorisCover) : MapOfPairs c.pairAB c.pairB where
  toFun := fun x => ⟨x.1, x.2.2⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  mapsTo := fun _ h => h.elim

/-- The inclusion of pairs `(A, ∅) ↪ (X, ∅)`, which underlies the map
`i_1 : H_n(A) → H_n(X)` in the Mayer-Vietoris sequence. -/
def MayerVietorisCover.inclA_X (c : MayerVietorisCover) : MapOfPairs c.pairA c.pairX where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ h => h.elim

/-- The inclusion of pairs `(B, ∅) ↪ (X, ∅)`, which underlies the map
`i_2 : H_n(B) → H_n(X)` in the Mayer-Vietoris sequence. -/
def MayerVietorisCover.inclB_X (c : MayerVietorisCover) : MapOfPairs c.pairB c.pairX where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ h => h.elim

end MayerVietoris
