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
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part4


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


structure HexHighestCut (K : ℝ) where
  
  D : Type
  
  B : Type
  
  wtγ : D → ℝ
  
  wtB : B → ℝ
  
  wtB_nn : ∀ b, 0 ≤ wtB b
  
  wtγ_nn : ∀ d, 0 ≤ wtγ d
  
  split : D → B × B
  
  split_inj : Function.Injective split
  
  weight_bound : ∀ d, wtγ d ≤ K * (wtB (split d).1 * wtB (split d).2)
  
  D_summable : Summable wtγ
  
  B_summable : Summable wtB

end StatMech.Universality
