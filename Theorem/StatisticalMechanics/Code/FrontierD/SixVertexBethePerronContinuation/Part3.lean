/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexInfinityGraph_adj_noAdjacent
    {N n : Nat} {x y : SixVertexSector N n}
    (hxy : (sixVertexInfinityGraph N n).Adj x y) :
    SixVertexSectorNoAdjacent x ∧ SixVertexSectorNoAdjacent y := by
  have hdisj :=
    (sixVertexSectorRowDistance_eq_twice_iff_disjoint N n x y).mp hxy.2.2
  rcases hxy.2.1 with hforward | hforward
  · exact sixVertexSectorNoAdjacent_pair_of_forward_disjoint
      x y hforward hdisj
  · have h := sixVertexSectorNoAdjacent_pair_of_forward_disjoint
      y x hforward hdisj.symm
    exact ⟨h.2, h.1⟩


end
end StatMech.FrontierD
