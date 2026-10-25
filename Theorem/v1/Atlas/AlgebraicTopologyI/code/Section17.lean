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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section17.Part2


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- In degree $0$, the image subgroup is trivial: $\partial_1 = 0$ on $C_0(\mathbf{RP}^n)$. -/
lemma rpnImageSubgroup_zero (n : ℕ) : rpnImageSubgroup n 0 = ⊥ := by
  unfold rpnImageSubgroup; simp [Nat.not_odd_zero]

/-- For odd $k$ with $k < n$, the image of $\partial_{k+1}$ is $2\mathbb{Z}$ (so $H_k = \mathbb{Z}/2$). -/
lemma rpnImageSubgroup_odd_lt {n k : ℕ} (hk : Odd k) (hkn : k < n) :
    rpnImageSubgroup n k = AddSubgroup.zmultiples (2 : ℤ) := by
  unfold rpnImageSubgroup
  simp [show ¬(k > n) from by omega, show k ≠ n from by omega, hk]

/-- In the top degree $k = n$, the image of $\partial_{n+1} = 0$ is trivial. -/
lemma rpnImageSubgroup_self (n : ℕ) : rpnImageSubgroup n n = ⊥ := by
  unfold rpnImageSubgroup; simp

end RealProjectiveSpace
end
