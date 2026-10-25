/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Def.StatisticalMechanics.Code.IsingFK.BetacPc.Part2
open Real


namespace StatMech

namespace IsingFK

@[simp]
theorem mem_zeroMagnetizationSet {mStar : ℝ → ℝ} {β : ℝ} :
    β ∈ {β : ℝ | 0 < β ∧ mStar β = 0} ↔ 0 < β ∧ mStar β = 0 :=
  Iff.rfl


theorem betaC_eq (mStar : ℝ → ℝ) (q pc : ℝ)
    (hnonneg : ∀ β, 0 ≤ mStar β)
    (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β))
    (hpos : 0 < pToBeta q pc) :
    betaC mStar = pToBeta q pc := by
  unfold betaC
  have hset : {β : ℝ | 0 < β ∧ mStar β = 0} = Set.Ioc 0 (pToBeta q pc) := by
    ext β
    simp only [Set.mem_setOf_eq, Set.mem_Ioc]
    refine and_congr_right fun hβ => ?_
    
    have hzero_iff : mStar β = 0 ↔ ¬ (0 < mStar β) := by
      constructor
      · intro h; rw [h]; exact lt_irrefl 0
      · intro h; exact le_antisymm (not_lt.mp h) (hnonneg β)
    rw [hzero_iff, hpos_iff β hβ, not_lt]
  rw [hset, csSup_Ioc hpos]


theorem betaC_eq_log (mStar : ℝ → ℝ) (q pc : ℝ)
    (hnonneg : ∀ β, 0 ≤ mStar β)
    (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β))
    (hpos : 0 < pToBeta q pc) :
    betaC mStar = -((q - 1) / q) * Real.log (1 - pc) :=
  betaC_eq mStar q pc hnonneg hpos_iff hpos


theorem magnetization_pos_iff (mStar : ℝ → ℝ) (q pc p : ℝ) (hq : 1 < q)
    (hp : p ∈ Set.Ico (0 : ℝ) 1) (hpc : pc ∈ Set.Ico (0 : ℝ) 1)
    (hβpos : 0 < pToBeta q p)
    (hpos_iff : ∀ β, 0 < β → (0 < mStar β ↔ pToBeta q pc < β)) :
    0 < mStar (pToBeta q p) ↔ pc < p := by
  rw [hpos_iff _ hβpos]
  exact (strictMonoOn_pToBeta q hq).lt_iff_lt (Set.mem_Iio.mpr hpc.2) (Set.mem_Iio.mpr hp.2)


end IsingFK
end StatMech
