/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching
open Finset


namespace StatMech.FrontierD

noncomputable section

def FiniteKeyCapacityExpandedRelated
    {Key : Type*} {sourceCapacity targetCapacity : Key -> Nat}
    (related : Key -> Key -> Prop)
    (source : FiniteKeyCapacityCopies Key sourceCapacity)
    (target : FiniteKeyCapacityCopies Key targetCapacity) : Prop :=
  related source.1 target.1

def sigmaFinFiberEquiv
    {Key : Type*} (capacity : Key -> Nat) (key : Key) :
    {source : FiniteKeyCapacityCopies Key capacity // source.1 = key} ≃
      Fin (capacity key) where
  toFun source := Fin.cast (congrArg capacity source.property) source.1.2
  invFun index := ⟨⟨key, index⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨sourceKey, index⟩, hkey⟩
    cases hkey
    rfl
  right_inv index := by rfl

end
end StatMech.FrontierD
