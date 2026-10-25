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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section15.Part5
open Topology


namespace SphereInfty

/-- Given a nonzero finitely supported vector $v \in \mathbb{R}^{\infty}$, its
normalization $v / \|v\|$ as a point of $S^{\infty}$. -/
def normalizeToSphere (v : l2) (hv : v ≠ 0) (hR : v ∈ RInfty) : Sphere :=
  ⟨‖v‖⁻¹ • v, RInfty.smul_mem _ hR, norm_normalize v hv⟩


/-- The straight-line family in $\ell^2$ joining $T x$ to $x$: at time $t$, the
vector $t \cdot x + (1 - t) \cdot T x$. After normalization this gives the
homotopy from $T$ (at $t = 0$) to the identity (at $t = 1$) on $S^{\infty}$. -/
def v_id_T (p : I × Sphere) : l2 :=
  (p.1 : ℝ) • (p.2.1 : l2) + (1 - (p.1 : ℝ)) • T (p.2.1 : l2)

end SphereInfty
