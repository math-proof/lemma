/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUnitComponentHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
open Finset


namespace StatMech.FrontierD

noncomputable section

def booleanMiddleLayerDownRelation
    {Component : Type*} [Fintype Component]
    {k : Nat} (source : BooleanLayer Component (k + 1))
    (target : BooleanLayer Component k) : Prop :=
  target.1 ⊆ source.1


noncomputable def booleanMiddleLayerAddedElement
    {Component : Type*} [Fintype Component]
    {k : Nat} (target : BooleanLayer Component k)
    (source : BooleanLayer Component (k + 1)) : Component := by
  have hcard : target.1.card < source.1.card := by
    rw [target.2, source.2]
    omega
  exact Classical.choose
    (Finset.exists_mem_notMem_of_card_lt_card hcard)

end
end StatMech.FrontierD
