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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part12
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwOrderedPortInternalGraphHom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    kwOrderedPortInternalGraph G order →g
      SimpleGraph.pathGraph
        (Fintype.card V * (Fintype.card (KWDartPort G) + 1)) where
  toFun := kwOrderedPortForestCode G order
  map_rel' := by
    rintro p q ⟨hfst, hrank⟩
    rw [SimpleGraph.pathGraph_adj]
    rcases hrank with hrank | hrank
    · left
      dsimp only [kwOrderedPortForestCode]
      rw [hfst]
      omega
    · right
      dsimp only [kwOrderedPortForestCode]
      rw [hfst]
      omega


end StatMech.FrontierA
