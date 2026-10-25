/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jfc_whbSync_step_of_evenContour (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKle : K ≤ P.G) {x y : P.V} (hadjG : P.G.Adj x y) (hnotK : ¬ K.Adj x y) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y))
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) (jei_pushGraph_edgeSet_finite P K).toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
    (K.Reachable x y ↔
      ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0) := by
  classical
  haveI := jfc_pushGraph_locallyFinite P K hKle
  haveI hft : Fintype (jei_pushGraph P K).edgeSet := (jei_pushGraph_edgeSet_finite P K).fintype
  have htoFinset : @Set.toFinset _ (jei_pushGraph P K).edgeSet hft
      = (jei_pushGraph_edgeSet_finite P K).toFinset := by
    apply Finset.ext; intro e
    rw [Set.mem_toFinset, Set.Finite.mem_toFinset]
  rw [← htoFinset] at hcc
  have hnpq : s(P.emb x, P.emb y) ∉ (jei_pushGraph P K).edgeSet := by
    rw [SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
    rintro ⟨u, v, hKuv, hu, hv⟩
    exact hnotK ((P.emb.injective hu) ▸ (P.emb.injective hv) ▸ hKuv)
  have hbicond := jeb_correctWhitney_of_evenDegree (jei_pushGraph P K)
    (jfc_pushGraph_le_lattice P K hKle) (P.emb x) (P.emb y) f0 g0 (P.isSub hadjG) hnpq hfg
    hshared hcc
  rwa [jei_push_reachable_iff P K x y] at hbicond


end Lattice
end StatMech
