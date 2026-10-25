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
open Finset BigOperators Set Metric


namespace AlgebraicTopologyI

/-- The barycenter of `n + 1` points `v 0, …, v n` in a real normed space:
the average `(n + 1)⁻¹ · Σ v i`. -/
def barycenter (n : ℕ) (v : Fin (n + 1) → E) : E :=
  (↑(n + 1) : ℝ)⁻¹ • ∑ i : Fin (n + 1), v i

end AlgebraicTopologyI
