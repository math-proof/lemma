/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.Homology.AlternatingConst
import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section5.Part3
open CategoryTheory

universe u₀


namespace HomotopyTheory

/-- **Definition 5.6** (Contractible). A space `X` is contractible if the unique map
`X → *` is a homotopy equivalence; equivalently, `X` is homotopy equivalent to a point.
Realized here as Mathlib's `ContractibleSpace`. -/
abbrev IsContractible (X : Type*) [TopologicalSpace X] : Prop :=
  ContractibleSpace X

/-- **Definition 5.4** (Homotopy equivalence). A homotopy equivalence between `X` and
`Y` is a pair of continuous maps `f : X → Y` and `g : Y → X` with `g ∘ f ≃ idₓ` and
`f ∘ g ≃ id_Y`. Bundled here as Mathlib's `ContinuousMap.HomotopyEquiv`. -/
abbrev HomotopyEquivalence (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  ContinuousMap.HomotopyEquiv X Y

end HomotopyTheory
