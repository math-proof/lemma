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
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part5


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


structure HexHWData (c : ℕ → ℝ) (υ : ℕ → ℝ) (x : ℝ) (N : ℕ) where
  
  S : Type
  
  Dn : Type
  
  Dn_fintype : Fintype Dn
  
  wtγ : Dn → ℝ
  
  wtS : S → ℝ
  
  wtγ_nn : ∀ d, 0 ≤ wtγ d
  
  wtS_nn : ∀ s, 0 ≤ wtS s
  
  S_summable : Summable wtS
  
  partial_eq : ∑ d, wtγ d = ∑ n ∈ Finset.range N, c n * x ^ n
  
  half_sum_eq : (∑' s, wtS s) = ∏' T, (1 + υ T)
  
  decomp : Dn → S × S
  
  decomp_inj : Function.Injective decomp
  
  weight_bound : ∀ d, wtγ d ≤ wtS (decomp d).1 * wtS (decomp d).2

end StatMech.Universality
