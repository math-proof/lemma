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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section17.Part3


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- Unfold the underlying vector of the antipodal map. -/
lemma sphereNeg_val (n : ℕ) (x : Sphere n) :
    (↑(sphereNeg n x) : EuclideanSpace ℝ (Fin (n + 1))) = -↑x := rfl

/-- The antipodal map on $S^n$ is an involution. -/
lemma sphereNeg_involutive (n : ℕ) : Function.Involutive (sphereNeg n) := by
  intro x; apply Subtype.ext; simp [sphereNeg_val, neg_neg]

/-- The antipodal map on $S^n$ is continuous. -/
lemma continuous_sphereNeg (n : ℕ) : Continuous (sphereNeg n) := by
  apply Continuous.subtype_mk
  exact continuous_neg.comp continuous_subtype_val

end RealProjectiveSpace
end
