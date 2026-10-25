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
set_option autoImplicit false


namespace YoungLattice

namespace Lmn

def shiftDown {m n : ℕ} (p : Lmn (m + 1) (n + 1)) (h : p.val (Fin.last m) ≠ 0) :
    Lmn (m + 1) n :=
  ⟨fun i => ⟨(p.val i).val - 1, by
    have hpos : 0 < (p.val (Fin.last m)).val := Fin.pos_iff_ne_zero.mpr h
    have hle := p.property (Fin.le_last i); have := (p.val i).isLt; omega⟩,
   fun a b hab => by simp only [Fin.le_def]; have := p.property hab; omega⟩

def shiftUp {m n : ℕ} (q : Lmn (m + 1) n) : Lmn (m + 1) (n + 1) :=
  ⟨fun i => ⟨(q.val i).val + 1, by have := (q.val i).isLt; omega⟩,
   fun a b hab => by simp only [Fin.le_def]; have := q.property hab; omega⟩

def restrictToInit {m n : ℕ} (p : Lmn (m + 1) (n + 1))
    (_h : p.val (Fin.last m) = 0) : Lmn m (n + 1) :=
  ⟨fun i => p.val (Fin.castSucc i),
   fun _ _ hab => p.property (Fin.castSucc_le_castSucc_iff.mpr hab)⟩

def extendZero {m n : ℕ} (q : Lmn m (n + 1)) : Lmn (m + 1) (n + 1) :=
  ⟨Fin.snoc q.val (0 : Fin (n + 2)),
   fun a b (hab : a ≤ b) => by
    rcases Fin.eq_castSucc_or_eq_last b with ⟨j, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact q.property (Fin.castSucc_le_castSucc_iff.mp hab)
      · exact absurd hab (not_le.mpr (Fin.castSucc_lt_last j))
    · simp only [Fin.snoc_last]; exact Fin.zero_le _⟩

end Lmn
end YoungLattice
