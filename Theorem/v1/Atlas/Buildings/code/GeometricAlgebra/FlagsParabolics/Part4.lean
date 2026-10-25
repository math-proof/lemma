/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Group
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part4


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

namespace Flag

/-- The length of `F.truncate h` is `F.len - 1`. -/
@[simp] lemma truncate_len (F : Flag k V) (h : 1 ≤ F.len) :
    (F.truncate h).len = F.len - 1 := rfl

/-- The length of `F.truncateStart h` is `F.len - 1`. -/
@[simp] lemma truncateStart_len (F : Flag k V) (h : 1 ≤ F.len) :
    (F.truncateStart h).len = F.len - 1 := rfl

/-- The spaces of `F.truncate h` agree with those of `F` at the same indices. -/
theorem truncate_spaces (F : Flag k V) (h : 1 ≤ F.len) (i : Fin (F.len - 1)) :
    (F.truncate h).spaces i = F.spaces ⟨i.val, by omega⟩ :=
  rfl

/-- The spaces of `F.truncateStart h` are `F.spaces ⟨i + 1, …⟩`. -/
theorem truncateStart_spaces (F : Flag k V) (h : 1 ≤ F.len) (i : Fin (F.len - 1)) :
    (F.truncateStart h).spaces i = F.spaces ⟨i.val + 1, by omega⟩ :=
  rfl

end Flag
end GeometricAlgebra
