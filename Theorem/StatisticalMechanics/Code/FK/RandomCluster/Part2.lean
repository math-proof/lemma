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
public import Def.StatisticalMechanics.Code.FK.RandomCluster.Part2
open scoped BigOperators

public section

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in


theorem edgeProduct_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (ω : ConfigSpace (Sym2 V)) :
    0 < edgeProduct G p ω := by
  unfold edgeProduct
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · linarith


end FK
end StatMech
