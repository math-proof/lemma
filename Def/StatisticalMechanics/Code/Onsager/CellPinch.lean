/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellPinch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3


namespace StatMech.Onsager.CellPinch

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


def pinchAt (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : Prop :=
  (v ∈ S ∧ (v.1 - 1, v.2 - 1) ∈ S ∧ (v.1 - 1, v.2) ∉ S ∧ (v.1, v.2 - 1) ∉ S) ∨
    ((v.1 - 1, v.2) ∈ S ∧ (v.1, v.2 - 1) ∈ S ∧ v ∉ S ∧ (v.1 - 1, v.2 - 1) ∉ S)

end StatMech.Onsager.CellPinch
