module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.FKG
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.DensityBounds
public import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal
open scoped BigOperators
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def bcEventMass (C : SimpleGraph V) [DecidableRel C.Adj] (p q : ℝ)
    (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), A.indicator (fun _ => (1 : ℝ)) ω * bcProb G C p q ω

end FK
end StatMech
