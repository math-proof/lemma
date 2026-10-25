/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable instance kwDartPortSplitGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (kwDartPortSplitGraph G).Adj :=
  Classical.decRel _

end StatMech.FrontierA
