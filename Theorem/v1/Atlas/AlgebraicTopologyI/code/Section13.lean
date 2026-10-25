/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section12
import Def.v1.Atlas.AlgebraicTopologyI.code.Section12.Part2
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Module.Convex
import Def.v1.Atlas.AlgebraicTopologyI.code.Section13.Part2
open Finset BigOperators Set Metric


namespace AlgebraicTopologyI

/-- The `0`-th iterate of `f` is the identity. -/
@[simp]
theorem endoPow_zero
    {C : ChainComplex AddCommGrpCat ℕ} (f : C ⟶ C) :
    endoPow f 0 = 𝟙 C := rfl

end AlgebraicTopologyI
