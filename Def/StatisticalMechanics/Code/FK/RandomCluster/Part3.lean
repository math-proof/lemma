/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part2

@[expose] public section

open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


def fkWeight (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  edgeProduct G p ω * q ^ numClusters G ω


end FK
end StatMech
