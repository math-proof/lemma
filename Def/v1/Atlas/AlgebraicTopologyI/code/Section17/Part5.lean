/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section17.Part2


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- Auxiliary vector in $\mathbb{R}^{n+1}$ used to define the $k$-cell characteristic map:
$x \in B^k$ (i.e.\ first $k$ coordinates) gets extended by $1 - \|x\|$ in the $k$th slot and
zeros afterwards. -/
def rpnRawVec (n k : ℕ) (_hk : k ≤ n) (x : Fin k → ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (fun i : Fin (n + 1) =>
    if h : (i : ℕ) < k then x ⟨i, h⟩
    else if (i : ℕ) = k then 1 - ‖x‖
    else 0)

end RealProjectiveSpace
end
