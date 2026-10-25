/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungDiagrams.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Sum
import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungDiagrams
set_option autoImplicit false


namespace YoungLattice

namespace Lmn

lemma extendZero_last {m n : ℕ} (q : Lmn m (n + 1)) :
    (extendZero q).val (Fin.last m) = 0 := by
  simp [extendZero, Fin.snoc_last]

lemma shiftUp_last_ne_zero {m n : ℕ} (q : Lmn (m + 1) n) :
    (shiftUp q).val (Fin.last m) ≠ 0 := by
  simp only [shiftUp, ne_eq, Fin.ext_iff, Fin.val_zero]; omega

end Lmn
end YoungLattice
