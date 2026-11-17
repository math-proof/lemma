/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.FKG
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.DensityBounds
public import Def.StatisticalMechanics.Code.FK.EdgeMarginal
public section

open scoped BigOperators
open SimpleGraph


namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]


structure IsMonotoneCouplingFun (P : ConfigSpace E × ConfigSpace E → ℝ)
    (μ ν : ConfigSpace E → ℝ) : Prop where
  
  nonneg : ∀ z, 0 ≤ P z
  
  supportLE : ∀ z, ¬ z.1 ≤ z.2 → P z = 0
  
  fst_marginal : ∀ ω, ∑ ω' : ConfigSpace E, P (ω, ω') = μ ω
  
  snd_marginal : ∀ ω', ∑ ω : ConfigSpace E, P (ω, ω') = ν ω'


end FK
end StatMech
