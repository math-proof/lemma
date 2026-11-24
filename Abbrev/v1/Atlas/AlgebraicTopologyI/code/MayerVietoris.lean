module
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Def.v1.Atlas.AlgebraicTopologyI.code.MayerVietoris.Part2
open Set Topology EilenbergSteenrod Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u


namespace MayerVietoris

attribute [instance] MayerVietorisCover.instTop

/-- The excised pair `(X \ Bᶜ, A \ Bᶜ)`, abbreviated `EP`, used as the intermediate
pair through which the connecting homomorphism is factored. -/
abbrev MayerVietorisCover.EP (c : MayerVietorisCover) : TopPair :=
  c.pairXA.excisePair c.Bᶜ

end MayerVietoris
