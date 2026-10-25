/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc50arminjection.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc51_subgraph_isAcyclic {V : Type*} {T T' : SimpleGraph V} (hsub : T ≤ T')
    (h : T'.IsAcyclic) : T.IsAcyclic :=
  h.anti hsub


theorem bc51_arms_vertexDisjoint (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x c0 c1 z0 z1 : Site d}
    (w0 : T.Walk c0 z0) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1x : x ∉ w1.support)
    (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
    ∀ v, v ∈ w0.support → v ∈ w1.support → False :=
  sfa_armWalks_disjoint ω T hπ w0 hw0x w1 hw1x hcut


theorem bc51_arms_edgeDisjoint (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x c0 c1 z0 z1 : Site d}
    (w0 : T.Walk c0 z0) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1x : x ∉ w1.support)
    (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
    ∀ e, e ∈ w0.edges → e ∈ w1.edges → False := by
  intro e he0 he1
  
  have hd := bc51_arms_vertexDisjoint ω T hπ w0 hw0x w1 hw1x hcut
  induction e using Sym2.ind with
  | _ u v =>
    exact hd u (w0.fst_mem_support_of_mem_edges he0) (w1.fst_mem_support_of_mem_edges he1)


end StatMech.Walls
