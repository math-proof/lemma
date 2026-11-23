/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Structure.v1.Atlas.AlgebraicTopologyI.code.MayerVietoris.Part2

@[expose] public section

open Set Topology EilenbergSteenrod Function

universe u


namespace MayerVietoris

attribute [instance] MayerVietorisCover.instTop

/-- The pair `(X, A)` extracted from a Mayer-Vietoris cover, used as the input to the
excision axiom that drives the construction of the connecting homomorphism. -/
def MayerVietorisCover.pairXA (c : MayerVietorisCover) : TopPair where
  space := c.X
  instTop := c.instTop
  sub := c.A

end MayerVietoris
