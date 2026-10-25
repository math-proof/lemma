/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section15.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.UnitInterval
import Def.v1.Atlas.AlgebraicTopologyI.code.Section15.Part4
open Topology


namespace SphereInfty

/-- The shift operator $T$ preserves $\ell^2$-norm: $\|T x\| = \|x\|$. -/
lemma T_norm (x : l2) : ‖T x‖ = ‖x‖ := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]; congr 1
  rw [(lp.memℓp (T x)).summable hp |>.tsum_eq_zero_add]
  simp only [T, shiftRight, norm_zero, Real.zero_rpow (ne_of_gt hp), zero_add]

/-- `T` preserves $\mathbb{R}^{\infty}$: the shift of a finitely supported
sequence is finitely supported. -/
lemma T_mem_RInfty {x : l2} (hx : x ∈ RInfty) : T x ∈ RInfty :=
  finite_support_shiftRight hx

/-- The shift $T$ maps $S^{\infty}$ to itself: it preserves both finite support
and unit norm. -/
lemma T_mem_sphere_set (x : Sphere) :
    T x.1 ∈ RInfty ∩ Metric.sphere (0 : l2) 1 :=
  ⟨T_mem_RInfty x.mem_RInfty, by
    rw [Metric.mem_sphere, dist_zero_right, T_norm]; exact norm_eq_one x⟩

end SphereInfty
