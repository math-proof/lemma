/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/SelfDualityNode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.RSW.SelfDualityNode.Part4
open scoped BigOperators ENNReal NNReal
open MeasureTheory


namespace StatMech

namespace RSW

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

@[simp] theorem rsd_edgeCompl_invol (ω : ConfigSpace (Sym2 V)) :
    rsd_edgeCompl (rsd_edgeCompl ω) = ω := by
  funext e; simp [rsd_edgeCompl]


end RSW
end StatMech
