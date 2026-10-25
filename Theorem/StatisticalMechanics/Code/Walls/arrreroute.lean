/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atsattachsurgery.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem arr_offPatch_Ksupport_of_K'support {K : Finset (Site 2)} {c f : Site 2}
    (hc : ¬ ats_faceHasCorner c f)
    (hf : f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support) :
    f ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support :=
  (ats_mem_support_insert_iff_of_notCorner hc).mp hf


theorem arr_offPatch_K'support_of_Ksupport {K : Finset (Site 2)} {c f : Site 2}
    (hc : ¬ ats_faceHasCorner c f)
    (hf : f ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support) :
    f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support :=
  (ats_mem_support_insert_iff_of_notCorner hc).mpr hf


theorem arr_offPatch_reachableK_of_anchor {K : Finset (Site 2)} {c a₀ : Site 2}
    (hreachK : fbc_BoundaryReachable (↑K : Set (Site 2)))
    (ha₀ : a₀ ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support)
    {f : Site 2} (hc : ¬ ats_faceHasCorner c f)
    (hf : f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support) :
    (faceBoundaryGraph (↑K : Set (Site 2))).Reachable f a₀ :=
  hreachK f a₀ (arr_offPatch_Ksupport_of_K'support hc hf) ha₀


theorem arr_hookB_of_adjToOffPatch {K : Finset (Site 2)} {c a₀ f g : Site 2}
    (hA' : ∀ w : Site 2, ¬ ats_faceHasCorner c w →
        w ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable w a₀)
    (hgc : ¬ ats_faceHasCorner c g)
    (hadj : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
  
  have hgsupp : g ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support :=
    ⟨f, hadj.symm⟩
  exact (SimpleGraph.Adj.reachable hadj).trans (hA' g hgc hgsupp)


theorem arr_hookB_of_hasOffPatchNeighbour {K : Finset (Site 2)} {c a₀ f : Site 2}
    (hA' : ∀ w : Site 2, ¬ ats_faceHasCorner c w →
        w ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable w a₀)
    (hhook : ∃ g : Site 2, ¬ ats_faceHasCorner c g ∧
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
  obtain ⟨g, hgc, hadj⟩ := hhook
  exact arr_hookB_of_adjToOffPatch hA' hgc hadj


theorem arr_hookB_of_reachOffPatch {K : Finset (Site 2)} {c a₀ f : Site 2}
    (hA' : ∀ w : Site 2, ¬ ats_faceHasCorner c w →
        w ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable w a₀)
    (hhook : ∃ g : Site 2, ¬ ats_faceHasCorner c g ∧
        g ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support ∧
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f g) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
  obtain ⟨g, hgc, hgsupp, hreach⟩ := hhook
  exact hreach.trans (hA' g hgc hgsupp)


end Walls
end StatMech
