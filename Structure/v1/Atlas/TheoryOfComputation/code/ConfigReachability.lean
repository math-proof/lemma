/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ConfigReachability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
open SpaceComplexity


namespace ConfigReachability

variable {Q : Type} {Γ : Type}

/-- An abstract directed graph whose vertices are configurations: a `Vertex` type with an
adjacency relation `Adj`. The configuration graph `G_{M,w}` of an NTM `M` on input `w` is the
instance with `Vertex = Config Q Γ` and `Adj = M.step`. -/
structure ConfigGraph (Q : Type) (Γ : Type) where
  Vertex : Type
  Adj : Vertex → Vertex → Prop

end ConfigReachability
