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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section11.Part2
open Set Topology

universe u


namespace EilenbergSteenrod

attribute [instance] TopPair.instTop

/-- A homotopy of pair maps `f₀, f₁ : (X, A) → (Y, B)`: a continuous map
`h : X × I → Y` interpolating from `f₀` to `f₁` such that `h(A × I) ⊆ B` at every time. -/
structure HomotopyOfPairMaps {P Q : TopPair} (f₀ f₁ : MapOfPairs P Q) where
  toFun : P.space × unitInterval → Q.space
  continuous_toFun : Continuous toFun
  map_zero : ∀ x, toFun (x, ⟨0, unitInterval.zero_mem⟩) = f₀.toFun x
  map_one : ∀ x, toFun (x, ⟨1, unitInterval.one_mem⟩) = f₁.toFun x
  mapsTo : ∀ (a : P.space), a ∈ P.sub → ∀ (t : unitInterval), toFun (a, t) ∈ Q.sub

end EilenbergSteenrod
