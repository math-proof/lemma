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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section15.Part6
open Topology


namespace SphereInfty

/-- The basis vector $e_1$ has unit norm. -/
lemma e1_norm : ‖e1‖ = 1 := by simp [e1, lp.norm_single]

/-- The basis vector $e_1$ has finite support, so lies in $\mathbb{R}^{\infty}$. -/
lemma e1_mem_RInfty : e1 ∈ RInfty := by
  apply Set.Finite.subset (Set.finite_singleton 0)
  intro n hn
  simp only [Function.mem_support, Set.mem_singleton_iff] at hn ⊢
  by_contra h; apply hn
  show (lp.single 2 0 (1 : ℝ) : ℕ → ℝ) n = 0
  simp [lp.single_apply, h]

/-- The basis vector $e_1$ lies in $S^{\infty}$, since it has unit norm and
finite support. -/
lemma e1_mem_sphere_set : e1 ∈ RInfty ∩ Metric.sphere (0 : l2) 1 :=
  ⟨e1_mem_RInfty, by rw [Metric.mem_sphere, dist_zero_right]; exact e1_norm⟩

/-- For a unit vector $x$ and any $t \in [0, 1]$, the affine combination
$t \cdot T x + (1 - t) \cdot e_1$ is nonzero. This ensures the straight-line
homotopy from the constant map $e_1$ to $T$ is well-defined after
normalization. -/
lemma norm_affine_T_e1_pos (x : l2) (hx : ‖x‖ = 1) (t : ℝ) (_ : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < ‖t • T x + (1 - t) • e1‖ := by
  rw [norm_pos_iff]; intro h
  have h0 : (t • T x + (1 - t) • e1).1 0 = 0 := congr_fun (congr_arg Subtype.val h) 0
  have h0' : 1 - t = 0 := by
    have : (t • T x + (1 - t) • e1).1 0 = 1 - t := by
      show t * (T x).1 0 + (1 - t) * e1.1 0 = 1 - t
      simp [T, shiftRight, e1, lp.single]
    linarith
  have ht_eq : t = 1 := by linarith
  subst ht_eq; simp at h
  linarith [show ‖T x‖ = 0 from by rw [h, norm_zero], T_norm x]


/-- A continuous family of nonzero vectors can be continuously normalized to
unit vectors. -/
lemma continuous_normalize_comp {α : Type*} [TopologicalSpace α]
    (v : α → l2) (hv_cont : Continuous v) (hv_ne : ∀ x, v x ≠ 0) :
    Continuous (fun x => ‖v x‖⁻¹ • v x) :=
  (Continuous.inv₀ (continuous_norm.comp hv_cont)
    (fun x => norm_ne_zero_iff.mpr (hv_ne x))).smul hv_cont

/-- Normalizing a nonzero vector yields a unit vector, i.e. a point on the unit
sphere in $\ell^2$. -/
lemma norm_normalize (v : l2) (hv : v ≠ 0) :
    ‖v‖⁻¹ • v ∈ Metric.sphere (0 : l2) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)


end SphereInfty
