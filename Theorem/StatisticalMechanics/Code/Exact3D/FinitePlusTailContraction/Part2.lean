/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part2
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace SummableTail

variable {α : Type*}


theorem summable_abs_sub (u v : SummableTail α) :
    Summable fun a => |u.coeff a - v.coeff a| := by
  have hdom : Summable fun a => |u.coeff a| + |v.coeff a| :=
    u.summable_abs.add v.summable_abs
  refine Summable.of_nonneg_of_le
    (fun a => abs_nonneg (u.coeff a - v.coeff a)) ?_ hdom
  intro a
  have h :
      |u.coeff a - v.coeff a| ≤ |u.coeff a| + |-v.coeff a| := by
    simpa [sub_eq_add_neg] using abs_add_le (u.coeff a) (-v.coeff a)
  simpa using h


theorem norm_nonneg (u : SummableTail α) : 0 ≤ u.norm :=
  tsum_nonneg fun a => abs_nonneg (u.coeff a)


theorem dist_nonneg (u v : SummableTail α) : 0 ≤ u.dist v :=
  tsum_nonneg fun a => abs_nonneg (u.coeff a - v.coeff a)


@[simp] theorem dist_self (u : SummableTail α) : u.dist u = 0 := by
  simp [dist]


@[simp] theorem dist_zero (u : SummableTail α) : u.dist 0 = u.norm := by
  unfold dist norm
  refine tsum_congr fun a => ?_
  simp


@[simp] theorem zero_dist (u : SummableTail α) : (0 : SummableTail α).dist u = u.norm := by
  unfold dist norm
  refine tsum_congr fun a => ?_
  simp


theorem dist_comm (u v : SummableTail α) : u.dist v = v.dist u := by
  unfold dist
  refine tsum_congr fun a => ?_
  rw [abs_sub_comm]


theorem abs_sub_coeff_le_dist (u v : SummableTail α) (a : α) :
    |u.coeff a - v.coeff a| ≤ u.dist v :=
  (u.summable_abs_sub v).le_tsum a (fun b _ => abs_nonneg (u.coeff b - v.coeff b))


theorem eq_of_dist_eq_zero {u v : SummableTail α}
    (h : u.dist v = 0) : u = v := by
  ext a
  have habs_nonpos : |u.coeff a - v.coeff a| ≤ 0 := by
    simpa [h] using abs_sub_coeff_le_dist u v a
  have habs_zero : |u.coeff a - v.coeff a| = 0 :=
    le_antisymm habs_nonpos (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs_zero)


theorem dist_triangle (u v w : SummableTail α) :
    u.dist w ≤ u.dist v + v.dist w := by
  have hright :
      Summable fun a =>
        |u.coeff a - v.coeff a| + |v.coeff a - w.coeff a| :=
    (u.summable_abs_sub v).add (v.summable_abs_sub w)
  have hle :
      ∀ a,
        |u.coeff a - w.coeff a| ≤
          |u.coeff a - v.coeff a| + |v.coeff a - w.coeff a| := by
    intro a
    have h :
        u.coeff a - w.coeff a =
          (u.coeff a - v.coeff a) + (v.coeff a - w.coeff a) := by
      ring
    rw [h]
    exact abs_add_le _ _
  calc
    u.dist w =
        ∑' a, |u.coeff a - w.coeff a| := rfl
    _ ≤
        ∑' a,
          (|u.coeff a - v.coeff a| + |v.coeff a - w.coeff a|) :=
      Summable.tsum_le_tsum hle (u.summable_abs_sub w) hright
    _ =
        (∑' a, |u.coeff a - v.coeff a|) +
          ∑' a, |v.coeff a - w.coeff a| :=
      (u.summable_abs_sub v).tsum_add (v.summable_abs_sub w)
    _ = u.dist v + v.dist w := rfl


end SummableTail
end Exact3D
end StatMech
