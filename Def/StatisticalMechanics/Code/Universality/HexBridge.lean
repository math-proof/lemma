/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Structure.StatisticalMechanics.Code.Universality.HexBridge


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


namespace HexColumn

variable {T : ℕ} {χ : ℝ}


noncomputable def colSum (C : HexColumn T χ) (y : ℝ) : ℝ := ∑' w, y ^ C.len w


end HexColumn
end StatMech.Universality
