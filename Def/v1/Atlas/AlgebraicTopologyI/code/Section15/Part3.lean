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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section15
open Topology


namespace SphereInfty

/-- The shift operator on sequences sending $(x_0, x_1, x_2, \ldots)$ to
$(0, x_0, x_1, \ldots)$. Used to build a sequence-level model of the operator
$T : \ell^2 \to \ell^2$ that underlies the contraction of $S^{\infty}$. -/
def shiftRight (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => x n

end SphereInfty
