/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def edgeProductOff (p : ℝ) (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ j ∈ G.edgeFinset.erase e, (if ω j then p else 1 - p)


end FK
end StatMech
