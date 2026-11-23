/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section12
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section12.Part2
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

open Finset BigOperators Set Metric


namespace AlgebraicTopologyI

/-- The barycenter of `n + 1` points `v 0, …, v n` in a real normed space:
the average `(n + 1)⁻¹ · Σ v i`. -/
def barycenter (n : ℕ) (v : Fin (n + 1) → E) : E :=
  (↑(n + 1) : ℝ)⁻¹ • ∑ i : Fin (n + 1), v i

end AlgebraicTopologyI
