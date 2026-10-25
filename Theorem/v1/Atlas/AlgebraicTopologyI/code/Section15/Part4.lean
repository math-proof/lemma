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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section15.Part5
open Topology


namespace SphereInfty

/-- Coordinate-level key lemma: if $t > 0$ and the affine combination
$t \cdot x + (1 - t) \cdot \text{shiftRight}(x)$ vanishes identically, then
$x = 0$. Used to prove that the affine homotopy from $\text{id}$ to $T$ never
passes through $0$. -/
lemma shiftRight_affine_zero_imp {x : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (h : ∀ n, t * x n + (1 - t) * shiftRight x n = 0) : ∀ n, x n = 0 := by
  intro n; induction n with
  | zero =>
    have h0 := h 0; simp [shiftRight] at h0
    exact h0.resolve_left (ne_of_gt ht)
  | succ n ih =>
    have hn := h (n + 1); simp [shiftRight] at hn
    rw [ih, mul_zero, add_zero] at hn
    exact (mul_eq_zero.mp hn).resolve_left (ne_of_gt ht)

/-- For a unit vector $x$ and any $t \in [0, 1]$, the affine combination
$t \cdot x + (1 - t) \cdot T x$ is nonzero. This ensures the straight-line
homotopy from $T$ to the identity is well-defined after normalization. -/
lemma norm_affine_id_T_pos (x : l2) (hx : ‖x‖ = 1) (t : ℝ) (ht0 : 0 ≤ t) (_ : t ≤ 1) :
    0 < ‖t • x + (1 - t) • T x‖ := by
  rw [norm_pos_iff]; intro h
  by_cases ht : t = 0
  · subst ht; simp at h
    linarith [show ‖T x‖ = 0 from by rw [h, norm_zero], T_norm x]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hcoord : ∀ n, (x : ℕ → ℝ) n = 0 :=
      shiftRight_affine_zero_imp ht_pos (fun n => congr_fun (congr_arg Subtype.val h) n)
    have hx0 : x = 0 := by ext n; exact hcoord n
    rw [hx0, norm_zero] at hx; exact one_ne_zero hx.symm


end SphereInfty
