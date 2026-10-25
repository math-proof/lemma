/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ChordCut.Part4


namespace StatMech.Onsager.ChordCut

open scoped BigOperators


def InteriorReaches (D : BoxData) (w : Pt) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B


end StatMech.Onsager.ChordCut
