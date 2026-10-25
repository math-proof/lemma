/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


@[simp] theorem mem_kwOrderedInternalNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p q : KWDartPort G) :
    q ∈ kwOrderedInternalNeighborFinset G order p ↔
      p.1 = q.1 ∧
        (kwOrderedPortRank order p + 1 = kwOrderedPortRank order q ∨
          kwOrderedPortRank order q + 1 = kwOrderedPortRank order p) := by
  simp [kwOrderedInternalNeighborFinset]


end StatMech.FrontierA
