/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.Universality.FrameChangeIso.Part2
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


@[simp] theorem fci_faceOpenDual_adj (ω : ConfigSpace (Sym2 (Site 2))) (f g : Site 2) :
    (fci_faceOpenDual ω).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ ω (sharedPrimalEdge f g) = false := Iff.rfl


theorem fci_faceOpenDual_le_dualLattice (ω : ConfigSpace (Sym2 (Site 2))) :
    fci_faceOpenDual ω ≤ dualLattice := fun _ _ h => h.1


theorem fci_faceBoundaryGraph_cluster_le (o : Site 2) :
    faceBoundaryGraph (cluster 2 ω o) ≤ fci_faceOpenDual ω := by
  rintro f g ⟨hlat, hbd⟩
  refine ⟨hlat, ?_⟩
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hlat
  rw [hpq] at hbd ⊢
  rw [bdEdge_mk] at hbd
  exact cluster_edgeBoundary_isClosed o ⟨hadj, hbd⟩


theorem fci_cluster_faceOpenDual_circuit (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    ∃ (u : Site 2) (c : (fci_faceOpenDual ω).Walk u u), c.IsCycle := by
  obtain ⟨u, c, hcyc, _⟩ := fdd_cluster_dualCircuit_open o hfin w hz
  exact ⟨u, c.mapLe (fci_faceBoundaryGraph_cluster_le o),
    hcyc.mapLe (fci_faceBoundaryGraph_cluster_le o)⟩


theorem fci_leftReach_faceOpenDual_adj_of_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {f g : Site 2} (h : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
    (hcl : ω (sharedPrimalEdge f g) = false) :
    (fci_faceOpenDual ω).Adj f g :=
  ⟨h.1, hcl⟩


theorem fci_leftReach_faceOpenDual_cycle (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle :=
  fdd_leftReach_dualCircuit ω n hn hnoH


end Universality
end StatMech
