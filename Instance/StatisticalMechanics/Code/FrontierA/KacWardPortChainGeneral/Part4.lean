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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part8
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable instance KWOrderedInternalSplitDart_decidableEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    DecidableEq (KWOrderedInternalSplitDart G order) :=
  Classical.decEq _

noncomputable instance KWOrderedInternalSplitDart_fintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    Fintype (KWOrderedInternalSplitDart G order) := by
  classical
  unfold KWOrderedInternalSplitDart
  infer_instance


end StatMech.FrontierA
