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
import Theorem.StatisticalMechanics.Code.Universality.HexBridge


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


structure HexColumn (T : ℕ) (χ : ℝ) where
  
  W : Type
  
  len : W → ℕ
  
  len_ge : ∀ w, T ≤ len w
  
  crit_summable : Summable (fun w => χ ^ len w)
  
  crit_le_one : (∑' w, χ ^ len w) ≤ 1

end StatMech.Universality
