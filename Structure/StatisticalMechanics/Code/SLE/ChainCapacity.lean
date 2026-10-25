/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerCapacity
import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
open Complex Set Filter Topology MeasureTheory
open scoped NNReal


namespace StatMech.SLE

structure IsCapacityParametrized (c : LoewnerChain) (a₁ : ℝ → ℝ) : Prop where
  

  normalized : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (c.maps t) (a₁ t)
  
  rate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t


end StatMech.SLE
