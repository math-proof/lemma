/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.ModelChains
import Def.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

open ContinuousMap

/-- Naturality of the cross product: for continuous maps `f : X → X'` and
`g : Y → Y'`, the cross product commutes with the induced maps on singular
chains, i.e. `f_*(a) × g_*(b) = (f × g)_*(a × b)`. This is the naturality
part of Theorem 6.2. -/
structure SingularChainHomotopy {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f0 f1 : C(X, Y)) where
  hom : ∀ (n : ℕ), SingularChains n X →+ SingularChains (n + 1) Y
  chain_htpy : ∀ (n : ℕ) (s : SingularChains (n + 1) X),
    boundaryMap (n + 1) Y (hom (n + 1) s) + hom n (boundaryMap n X s) =
      SingularChains.map f1 s - SingularChains.map f0 s

end
end AlgebraicTopologyI
