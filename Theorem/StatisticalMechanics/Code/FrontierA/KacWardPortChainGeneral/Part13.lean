module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
public import Mathlib.Data.Finset.Sort
public import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part13
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOrderedPortInternalGraph_isAcyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    (kwOrderedPortInternalGraph G order).IsAcyclic :=
  (kw_pathGraph_isAcyclic _).comap
    (kwOrderedPortInternalGraphHom G order)
    (kwOrderedPortForestCode_injective G order)


end StatMech.FrontierA
