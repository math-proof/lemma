/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part4


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem add_nonnegative {I J : RatInterval}
    (hI : I.Nonnegative) (hJ : J.Nonnegative) :
    (add I J).Nonnegative := by
  simpa [Nonnegative, add] using add_nonneg hI hJ


theorem finsetSum_nonnegative {α : Type*} {s : Finset α}
    {I : α → RatInterval}
    (hI : ∀ a, a ∈ s → (I a).Nonnegative) :
    (finsetSum s I).Nonnegative := by
  simpa [Nonnegative, finsetSum] using
    Finset.sum_nonneg fun a ha => hI a ha


theorem mulNonneg_nonnegative {I J : RatInterval}
    (hI : I.Nonnegative) (hJ : J.Nonnegative) :
    (mulNonneg I J hI hJ).Nonnegative := by
  simpa [Nonnegative, mulNonneg] using mul_nonneg hI hJ

theorem point_memQ (q : ℚ) : (point q).MemQ q := by
  simp [point]

theorem point_memR (q : ℚ) : (point q).MemR (q : ℝ) := by
  simp [point, MemR]


theorem memR_of_memQ {I : RatInterval} {q : ℚ} (hq : I.MemQ q) :
    I.MemR (q : ℝ) := by
  exact ⟨by exact_mod_cast hq.1, by exact_mod_cast hq.2⟩


theorem point_nonnegative {q : ℚ} (hq : 0 ≤ q) : (point q).Nonnegative := by
  simpa [point, Nonnegative] using hq


theorem add_memQ {I J : RatInterval} {x y : ℚ}
    (hx : I.MemQ x) (hy : J.MemQ y) :
    (add I J).MemQ (x + y) := by
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩


theorem add_memR {I J : RatInterval} {x y : ℝ}
    (hx : I.MemR x) (hy : J.MemR y) :
    (add I J).MemR (x + y) := by
  constructor
  · simpa [MemR, add] using add_le_add hx.1 hy.1
  · simpa [MemR, add] using add_le_add hx.2 hy.2


theorem neg_memQ {I : RatInterval} {x : ℚ} (hx : I.MemQ x) :
    (neg I).MemQ (-x) := by
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩


theorem neg_memR {I : RatInterval} {x : ℝ} (hx : I.MemR x) :
    (neg I).MemR (-x) := by
  constructor
  · simpa [MemR, neg] using neg_le_neg hx.2
  · simpa [MemR, neg] using neg_le_neg hx.1


theorem sub_memQ {I J : RatInterval} {x y : ℚ}
    (hx : I.MemQ x) (hy : J.MemQ y) :
    (sub I J).MemQ (x - y) := by
  simpa [sub, sub_eq_add_neg] using add_memQ hx (neg_memQ hy)


theorem sub_memR {I J : RatInterval} {x y : ℝ}
    (hx : I.MemR x) (hy : J.MemR y) :
    (sub I J).MemR (x - y) := by
  simpa [sub, sub_eq_add_neg] using add_memR hx (neg_memR hy)


theorem finsetSum_memQ {α : Type*} {s : Finset α} {I : α → RatInterval}
    {x : α → ℚ} (hx : ∀ a, a ∈ s → (I a).MemQ (x a)) :
    (finsetSum s I).MemQ (s.sum fun a => x a) := by
  constructor
  · exact Finset.sum_le_sum fun a ha => (hx a ha).1
  · exact Finset.sum_le_sum fun a ha => (hx a ha).2


theorem finsetSum_memR {α : Type*} {s : Finset α} {I : α → RatInterval}
    {x : α → ℝ} (hx : ∀ a, a ∈ s → (I a).MemR (x a)) :
    (finsetSum s I).MemR (s.sum fun a => x a) := by
  constructor
  · simpa [finsetSum, MemR] using Finset.sum_le_sum fun a ha => (hx a ha).1
  · simpa [finsetSum, MemR] using Finset.sum_le_sum fun a ha => (hx a ha).2


theorem abs_le_absUpper_of_memQ {I : RatInterval} {q : ℚ} (hq : I.MemQ q) :
    |q| ≤ I.absUpper := by
  rw [abs_le]
  constructor
  · calc
      -I.absUpper ≤ -(-I.lower) := neg_le_neg (le_max_left (-I.lower) I.upper)
      _ = I.lower := by ring
      _ ≤ q := hq.1
  · exact le_trans hq.2 (le_max_right (-I.lower) I.upper)


theorem abs_le_absUpper_of_memR {I : RatInterval} {x : ℝ} (hx : I.MemR x) :
    |x| ≤ (I.absUpper : ℝ) := by
  rw [abs_le]
  constructor
  · have hleft : (-(I.absUpper) : ℝ) ≤ -(-I.lower : ℚ) := by
      exact neg_le_neg (by exact_mod_cast le_max_left (-I.lower) I.upper)
    have hlower : (-(-I.lower : ℚ) : ℝ) = I.lower := by norm_num
    calc
      (-(I.absUpper) : ℝ) ≤ (-(-I.lower : ℚ) : ℝ) := hleft
      _ = (I.lower : ℝ) := hlower
      _ ≤ x := hx.1
  · exact le_trans hx.2 (by exact_mod_cast le_max_right (-I.lower) I.upper)


theorem mul_memR {I J : RatInterval} {x y : ℝ}
    (hx : I.MemR x) (hy : J.MemR y) :
    (mul I J).MemR (x * y) := by
  have hIx := abs_le_absUpper_of_memR hx
  have hJy := abs_le_absUpper_of_memR hy
  have hprod' : |x * y| ≤ (I.absUpper : ℝ) * (J.absUpper : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hIx hJy (abs_nonneg y) (by exact_mod_cast I.absUpper_nonneg)
  have hprod : |x * y| ≤ ((I.absUpper * J.absUpper : ℚ) : ℝ) := by
    simpa using hprod'
  rw [abs_le] at hprod
  simpa [MemR, mul] using hprod


theorem mul_memQ {I J : RatInterval} {x y : ℚ}
    (hx : I.MemQ x) (hy : J.MemQ y) :
    (mul I J).MemQ (x * y) := by
  have hIx := abs_le_absUpper_of_memQ hx
  have hJy := abs_le_absUpper_of_memQ hy
  have hprod : |x * y| ≤ I.absUpper * J.absUpper := by
    rw [abs_mul]
    exact mul_le_mul hIx hJy (abs_nonneg y) I.absUpper_nonneg
  rw [abs_le] at hprod
  simpa [MemQ, mul] using hprod


theorem mulNonneg_memQ {I J : RatInterval} {x y : ℚ}
    (hI : I.Nonnegative) (hJ : J.Nonnegative)
    (hx : I.MemQ x) (hy : J.MemQ y) :
    (mulNonneg I J hI hJ).MemQ (x * y) := by
  have hx0 : 0 ≤ x := le_trans hI hx.1
  have hy0 : 0 ≤ y := le_trans hJ hy.1
  constructor
  · exact mul_le_mul hx.1 hy.1 hJ hx0
  · exact mul_le_mul hx.2 hy.2 hy0 (le_trans hI I.lower_le_upper)


theorem mulNonneg_memR {I J : RatInterval} {x y : ℝ}
    (hI : I.Nonnegative) (hJ : J.Nonnegative)
    (hx : I.MemR x) (hy : J.MemR y) :
    (mulNonneg I J hI hJ).MemR (x * y) := by
  have hIℝ : (0 : ℝ) ≤ I.lower := by exact_mod_cast hI
  have hJℝ : (0 : ℝ) ≤ J.lower := by exact_mod_cast hJ
  have hx0 : 0 ≤ x := le_trans hIℝ hx.1
  have hy0 : 0 ≤ y := le_trans hJℝ hy.1
  constructor
  · simpa [MemR, mulNonneg] using mul_le_mul hx.1 hy.1 hJℝ hx0
  · have hIupper : (0 : ℝ) ≤ I.upper := le_trans hIℝ (by exact_mod_cast I.lower_le_upper)
    simpa [MemR, mulNonneg] using mul_le_mul hx.2 hy.2 hy0 hIupper


end RatInterval
end Exact3D
end StatMech
