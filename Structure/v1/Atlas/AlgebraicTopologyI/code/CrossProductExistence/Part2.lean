/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.ModelChains
import Def.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence.Part2
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

open ContinuousMap

/-- A natural chain homotopy between the singular-chain maps induced by the
two inclusions `inclusion0, inclusion1 : X → X × I`. The data consists of
homomorphisms `S_n(X) → S_{n+1}(X × I)` satisfying the chain-homotopy
identity and a naturality square in `X`. This is the universal ingredient
used to build chain homotopies from continuous homotopies in Theorem 6.1. -/
structure NaturalChainHomotopyInclusions where
  hom : ∀ (X : Type) [TopologicalSpace X] (n : ℕ),
    SingularChains n X →+ SingularChains (n + 1) (X × ↥I)
  chain_htpy : ∀ (X : Type) [TopologicalSpace X] (n : ℕ)
    (s : SingularChains (n + 1) X),
    boundaryMap (n + 1) (X × ↥I) (hom X (n + 1) s) + hom X n (boundaryMap n X s) =
      SingularChains.map (inclusion1 X) s - SingularChains.map (inclusion0 X) s
  naturality : ∀ (X X' : Type) [TopologicalSpace X] [TopologicalSpace X']
    (g : C(X', X)) (n : ℕ) (s : SingularChains n X'),
    SingularChains.map (ContinuousMap.prodMap g (ContinuousMap.id ↥I)) (hom X' n s) =
      hom X n (SingularChains.map g s)

end
end AlgebraicTopologyI
