/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/GeometricRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
set_option linter.unusedSectionVars false


noncomputable section

open Finset BigOperators

namespace GeometricRealization

variable {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V]

/-- A **point** of the geometric realization $|\Delta|$ of a simplicial complex $\Delta$: a barycentric
weighting of vertices that sums to $1$ and whose support lies in some face of $\Delta$. -/
structure Point (Δ : SimplicialComplex V) where
  wt : V → ℝ
  wt_nonneg : ∀ v, wt v ≥ 0
  wt_sum : ∑ v : V, wt v = 1
  support_in_face : ∃ σ ∈ Δ.faces, ∀ v, wt v ≠ 0 → v ∈ σ

end GeometricRealization
end
