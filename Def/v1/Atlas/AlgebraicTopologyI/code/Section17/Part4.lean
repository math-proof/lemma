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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section17.Part2


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- The antipodal map as a self-homeomorphism of $S^n$. -/
def sphereNegHomeomorph (n : ℕ) : Sphere n ≃ₜ Sphere n :=
  Homeomorph.mk ((sphereNeg_involutive n).toPerm (sphereNeg n))
    (continuous_sphereNeg n)
    ((sphereNeg_involutive n).toPerm_symm ▸ continuous_sphereNeg n)

/-- Index type for the CW cells of $\mathbf{RP}^n$ in degree $k$: a single cell when
$k \le n$, none otherwise. -/
def RPnCell (n k : ℕ) : Type := if k ≤ n then PUnit else Empty

end RealProjectiveSpace
end
