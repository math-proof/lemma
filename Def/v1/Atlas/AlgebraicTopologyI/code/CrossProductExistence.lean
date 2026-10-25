/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.ModelChains
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

open ContinuousMap

/-- The singular chain cross product
`× : S_p(X) × S_q(Y) → S_{p+q}(X × Y)` as a bilinear map, defined on generators
by applying the universal model cross product to each pair of simplices and
extending freely. This is the underlying construction for Theorem 6.2. -/
noncomputable def crossProductMap (p q : ℕ) (X : Type) (Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] :
    SingularChains p X →+ (SingularChains q Y →+ SingularChains (p + q) (X × Y)) :=
  FreeAbelianGroup.lift (fun (σ : SingularSimplex p X) =>
    FreeAbelianGroup.lift (fun (τ : SingularSimplex q Y) =>
      crossFromModelChain (universalCross p q) σ τ))

end
end AlgebraicTopologyI
