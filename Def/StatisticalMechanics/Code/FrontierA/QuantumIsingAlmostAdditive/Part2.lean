/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive

@[expose] public section

open Filter Set


namespace StatMech.FrontierA

namespace QuantumIsingAlmostAdditive

variable {u : Nat -> Real} {c : Real}

noncomputable def limit (h : QuantumIsingAlmostAdditive u c) : Real :=
  (h.shift_subadditive).lim


end QuantumIsingAlmostAdditive
end StatMech.FrontierA
