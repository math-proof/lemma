module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientGroup
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section17.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- Each $\mathbf{RP}^n$ cell-index type is finite. -/
instance RPnCell.finite (n k : ℕ) : Finite (RPnCell n k) := by
  simp only [RPnCell]; split <;> infer_instance

end RealProjectiveSpace
end
