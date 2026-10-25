/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirectLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Constructions
import Mathlib.Order.Directed


namespace TopologicalSpace.DirectLimit

section BasicDefs

variable {ι : Type*} [Preorder ι]
  (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (f : ∀ i j, i ≤ j → X i → X j)

def Rel : (Σ i, X i) → (Σ i, X i) → Prop :=
  fun a b => ∃ (i j : ι) (h : i ≤ j) (x : X i),
    a = ⟨i, x⟩ ∧ b = ⟨j, f i j h x⟩

def directLimitSetoid : Setoid (Σ i, X i) :=
  Relation.EqvGen.setoid (Rel X f)

end BasicDefs
end TopologicalSpace.DirectLimit
