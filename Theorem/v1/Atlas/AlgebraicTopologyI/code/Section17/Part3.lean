/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Def.v1.Atlas.AlgebraicTopologyI.code.Section17.Part5


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- Component formula for `rpnRawVec`: the $i$th coordinate is $x_i$ for $i < k$, $1 - \|x\|$
for $i = k$, and $0$ for $i > k$. -/
lemma rpnRawVec_apply (n k : ℕ) (hk : k ≤ n) (x : Fin k → ℝ) (i : Fin (n + 1)) :
    (rpnRawVec n k hk x) i =
      if h : (i : ℕ) < k then x ⟨i, h⟩
      else if (i : ℕ) = k then 1 - ‖x‖
      else 0 := by
  simp [rpnRawVec, WithLp.equiv]

/-- The auxiliary vector `rpnRawVec` is never zero (so its normalisation is well-defined). -/
lemma rpnRawVec_ne_zero (n k : ℕ) (hk : k ≤ n) (x : Fin k → ℝ) :
    rpnRawVec n k hk x ≠ 0 := by
  intro h
  have hcomp : ∀ i : Fin (n+1), (rpnRawVec n k hk x) i = 0 := fun i => by
    have : rpnRawVec n k hk x = 0 := h
    simp [this]
  have hk_entry := hcomp ⟨k, by omega⟩
  rw [rpnRawVec_apply] at hk_entry
  simp at hk_entry

  have hnorm1 : ‖x‖ = 1 := by linarith
  by_cases hk0 : k = 0
  · subst hk0; simp [Pi.norm_def] at hnorm1
  · have hx_ne : x ≠ 0 := by intro hx0; simp [hx0] at hnorm1
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx_ne
    have hi_comp := hcomp ⟨i.val, by omega⟩
    rw [rpnRawVec_apply] at hi_comp
    simp [show (i : ℕ) < k from i.isLt] at hi_comp
    exact hi hi_comp

end RealProjectiveSpace
end
