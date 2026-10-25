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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section15.Part6
open Topology


namespace SphereInfty

/-- The straight-line family in $\ell^2$ joining $e_1$ to $T x$: at time $t$,
the vector $t \cdot T x + (1 - t) \cdot e_1$. After normalization this gives
the homotopy from the constant map $e_1$ (at $t = 0$) to $T$ (at $t = 1$) on
$S^{\infty}$. -/
def v_T_e1 (p : I × Sphere) : l2 :=
  (p.1 : ℝ) • T (p.2.1 : l2) + (1 - (p.1 : ℝ)) • e1

end SphereInfty
