/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirectLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Constructions
public import Mathlib.Order.Directed
public import Def.v1.Atlas.NumberTheoryI.code.DirectLimits

@[expose] public section


namespace TopologicalSpace.DirectLimit

abbrev Space {ι : Type*} [Preorder ι]
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (f : ∀ i j, i ≤ j → X i → X j) : Type _ :=
  @Quotient (Σ i, X i) (directLimitSetoid X f)

end TopologicalSpace.DirectLimit
