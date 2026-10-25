/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jgc_leaf_deleteEdges_isolated {V : Type*} {K : SimpleGraph V} {x z : V}
    (huniq : ∀ w, K.Adj x w → w = z) :
    ∀ w, ¬ (K.deleteEdges {s(x, z)}).Adj x w := by
  intro w hadjw
  rw [deleteEdges_adj] at hadjw
  obtain ⟨hKxw, hnotin⟩ := hadjw
  have hwz : w = z := huniq w hKxw
  subst hwz
  exact hnotin (by rw [Set.mem_singleton_iff])


theorem jgc_leaf_not_reachable {V : Type*} {K : SimpleGraph V} {x z : V} (hadj : K.Adj x z)
    (huniq : ∀ w, K.Adj x w → w = z) :
    ¬ (K.deleteEdges {s(x, z)}).Reachable x z := by
  have hxz : x ≠ z := K.ne_of_adj hadj
  rintro ⟨wk⟩
  have hxiso := jgc_leaf_deleteEdges_isolated huniq
  cases wk with
  | nil => exact hxz rfl
  | cons hh _ => exact hxiso _ hh


theorem jgc_faceCount_deleteLeaf {V : Type*} [Finite V] [DecidableEq V] (K : SimpleGraph V)
    {x z : V} (hadj : K.Adj x z) (huniq : ∀ w, K.Adj x w → w = z) :
    faceCount (K.deleteEdges {s(x, z)}) = faceCount K := by
  classical
  have hmem : s(x, z) ∈ K.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
  exact (faceCount_deleteEdges_of_isBridge K hmem (jgc_leaf_not_reachable hadj huniq)).1


theorem jgc_tc_deleteLeaf (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (hKle : K ≤ P.G)
    {x z : P.V} (hadj : K.Adj x z) (huniq : ∀ w, K.Adj x w → w = z) :
    jic_tc P (K.deleteEdges {s(x, z)}) = jic_tc P K := by
  classical
  set K' := K.deleteEdges {s(x, z)} with hK'
  have hmem : s(x, z) ∈ K.edgeSet := by rwa [SimpleGraph.mem_edgeSet]
  have hKeq : K = K' ⊔ edge x z := deleteEdges_sup_edge_eq K x z hmem
  have hxz : x ≠ z := K.ne_of_adj hadj
  
  have hiso : ∀ w, ¬ K'.Adj x w := jgc_leaf_deleteEdges_isolated huniq
  
  have hlat : (hypercubicLattice 2).Adj (P.emb x) (P.emb z) := P.isSub (hKle hadj)
  
  have hkeep := jic_tc_sup_edge_keep P K' hxz hlat hiso
  rw [hKeq, hkeep]


end Lattice
end StatMech
