/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerCapacity
import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.ChainCapacity
open Complex Set Filter Topology MeasureTheory
open scoped NNReal


namespace StatMech.SLE

structure CapacityParametrizedChain where
  
  chain : LoewnerChain
  
  hull : ℝ → Set ℂ
  
  coeff : ℝ → ℝ
  
  hull_isHull : ∀ t, IsCompactHull (hull t)
  
  hull_monotone : Monotone hull
  
  capacity : IsCapacityParametrized chain coeff


end StatMech.SLE
