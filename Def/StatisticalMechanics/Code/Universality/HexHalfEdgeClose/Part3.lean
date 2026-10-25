/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part2


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


def hhe_singleRight_memB : List ℤ → Prop := fun ts => ts = [(-1 : ℤ)] ∨ ts = []


def hhe_singleRight_halvesInColumn :
    HexHalvesInColumn 0 hexW2_singleRight_memD hhe_singleRight_memB where
  htake := by
    intro d
    have hd : d.1 = [(-1 : ℤ)] := d.2
    rw [hd, hhe_singleRight_cutPos]
    left; rfl
  hdrop := by
    intro d
    have hd : d.1 = [(-1 : ℤ)] := d.2
    rw [hd, hhe_singleRight_cutPos]
    right; rfl


end StatMech.Universality
