/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Onsager.ChordCut.Part4


namespace StatMech.Onsager.ChordCut

open scoped BigOperators


instance (D : BoxData) (w : Pt) (k : ℕ) : Decidable (stopEvent D w k) := by
  unfold stopEvent; infer_instance


end StatMech.Onsager.ChordCut
