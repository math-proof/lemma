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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.YoungDiagrams
set_option autoImplicit false


namespace YoungLattice

namespace Lmn

noncomputable def sumEquiv (m n : ℕ) :
    Lmn (m + 1) (n + 1) ≃ Lmn m (n + 1) ⊕ Lmn (m + 1) n := by
  classical
  exact
  { toFun := fun p =>
      if h : p.val (Fin.last m) = 0 then Sum.inl (restrictToInit p h)
      else Sum.inr (shiftDown p h)
    invFun := fun | Sum.inl q => extendZero q | Sum.inr q => shiftUp q
    left_inv := by
      intro p; simp only; split_ifs with h
      · apply Lmn.ext; intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simp [extendZero, restrictToInit, Fin.snoc_castSucc]
        · simp only [extendZero, Fin.snoc_last]; exact h.symm
      · apply Lmn.ext; intro i
        simp only [shiftUp, shiftDown]; apply Fin.ext; simp only []
        have hpos : 0 < (p.val (Fin.last m)).val := Fin.pos_iff_ne_zero.mpr h
        have hle := p.property (Fin.le_last i); omega
    right_inv := by
      intro s; rcases s with q | q
      · simp only
        have h := extendZero_last q; simp only [h, ↓reduceDIte]
        exact congrArg Sum.inl (by
          apply Lmn.ext; intro i
          simp [restrictToInit, extendZero, Fin.snoc_castSucc])
      · simp only
        have h := shiftUp_last_ne_zero q; simp only [h, ↓reduceDIte]
        exact congrArg Sum.inr (by
          apply Lmn.ext; intro i
          simp only [shiftDown, shiftUp]
          apply Fin.ext; simp only []; omega) }

end Lmn
end YoungLattice
