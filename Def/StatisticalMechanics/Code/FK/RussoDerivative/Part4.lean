module
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
public import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part3
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def fkProbOf (p q : ℝ) (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  fkMean G p q (A.indicator (fun _ => (1 : ℝ)))


end FK
end StatMech
