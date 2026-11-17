/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Integration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.OrderClosed
public import Theorem.StatisticalMechanics.Code.OSSS.Integration

@[expose] public section

open scoped BigOperators
open Real Set Finset Filter Topology

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Integration

noncomputable def meanLogTerm (fseq : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fseq i x / (i : ℝ)


end OSSS.Integration
end StatMech
