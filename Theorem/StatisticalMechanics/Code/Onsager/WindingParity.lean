/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPropIV.Part2


namespace StatMech.Onsager

open BigOperators


theorem wpar_odd_ne_zero {m : ℤ} (h : Odd m) : m ≠ 0 := by
  rintro rfl
  rcases h with ⟨k, hk⟩
  omega


theorem wpar_oddWinding_forces_winds (n : ℕ) (d : Fin (n + 1) → Fin 4)
    (m : ℤ) (hm : (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) = 4 * m)
    (hodd : Odd m) :
    (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) ≠ 0 := by
  rw [hm]
  have := wpar_odd_ne_zero hodd
  simpa using this


end StatMech.Onsager
