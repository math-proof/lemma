/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.NumberTheoryI.code.ProductFormula
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ProductFormula
import Structure.v1.Atlas.NumberTheoryI.code.DirichletSeries


noncomputable section

open scoped Classical

namespace ArakelovDivisor

variable {K : Type*} [Field K] {hG : IsGlobalField K}

def one : ArakelovDivisor K hG where
  val := fun _ => 1
  pos := fun _ => one_pos
  finite_support := by simp

def mul (c d : ArakelovDivisor K hG) : ArakelovDivisor K hG where
  val := fun v => c.val v * d.val v
  pos := fun v => mul_pos (c.pos v) (d.pos v)
  finite_support := by
    apply Set.Finite.subset (c.finite_support.union d.finite_support)
    intro v hv
    simp only [Set.mem_setOf_eq, Set.mem_union] at hv ⊢
    by_contra h
    push Not at h
    exact hv (by rw [h.1, h.2, mul_one])

def inv (c : ArakelovDivisor K hG) : ArakelovDivisor K hG where
  val := fun v => (c.val v)⁻¹
  pos := fun v => inv_pos.mpr (c.pos v)
  finite_support := by
    apply Set.Finite.subset c.finite_support
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    intro h
    exact hv (by rw [h, inv_one])

end ArakelovDivisor
end
