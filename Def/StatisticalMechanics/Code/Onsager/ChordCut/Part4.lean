/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Onsager.ChordCut


namespace StatMech.Onsager.ChordCut

open scoped BigOperators


def stopEvent (D : BoxData) (w : Pt) (k : ℕ) : Prop :=
  1 ≤ k ∧ (rayX w k ∈ D.B ∨ D.x1 < w.1 + (k : ℤ))

end StatMech.Onsager.ChordCut
