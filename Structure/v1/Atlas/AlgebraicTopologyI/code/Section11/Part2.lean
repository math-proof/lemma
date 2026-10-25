/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Mathlib.Topology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Exact
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.Prod
import Def.v1.Atlas.AlgebraicTopologyI.code.Section11
open Set Topology

universe u


namespace EilenbergSteenrod

attribute [instance] TopPair.instTop

/-- A morphism of pairs `(X, A) → (Y, B)`: a continuous map `f : X → Y` such that
`f(A) ⊆ B`. These are the morphisms in the category of pairs. -/
structure MapOfPairs (P Q : TopPair) where
  toFun : P.space → Q.space
  continuous_toFun : Continuous toFun
  mapsTo : MapsTo toFun P.sub Q.sub

end EilenbergSteenrod
