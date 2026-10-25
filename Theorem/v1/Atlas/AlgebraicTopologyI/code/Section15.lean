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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section15.Part3
open Topology


namespace SphereInfty

/-- The sum of two finitely supported sequences in $\ell^2$ is again finitely
supported; closure of $\mathbb{R}^{\infty}$ under addition. -/
lemma RInfty.add_mem {x y : l2} (hx : x ∈ RInfty) (hy : y ∈ RInfty) :
    x + y ∈ RInfty :=
  (hx.union hy).subset (Function.support_add _ _)

/-- Scaling a finitely supported sequence by a scalar preserves finite support;
closure of $\mathbb{R}^{\infty}$ under scalar multiplication. -/
lemma RInfty.smul_mem (c : ℝ) {x : l2} (hx : x ∈ RInfty) :
    c • x ∈ RInfty := by
  apply Set.Finite.subset hx
  intro n hn
  simp only [Function.mem_support] at hn ⊢
  intro hx_n; apply hn
  show (c • x : l2).1 n = 0; simp [hx_n]


/-- Every point of $S^{\infty}$ has $\ell^2$-norm equal to $1$. -/
lemma norm_eq_one (x : Sphere) : ‖(x.1 : l2)‖ = 1 := by
  have := x.2.2; rwa [Metric.mem_sphere, dist_zero_right] at this


end SphereInfty
