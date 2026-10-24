/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import sympy.atlas.StatisticalMechanics.Code.Foundations.ConfigSpace
import sympy.atlas.StatisticalMechanics.Code.Lattice.HypercubicLattice
import sympy.atlas.StatisticalMechanics.Code.Lattice.Clusters
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanEnclosure
import sympy.atlas.StatisticalMechanics.Code.Lattice.LeftFace
import sympy.atlas.StatisticalMechanics.Code.Lattice.ContourAnchor
import sympy.atlas.StatisticalMechanics.Code.Lattice.ContourLinksExits
import sympy.atlas.StatisticalMechanics.Code.Lattice.BoundaryConnected
import sympy.atlas.StatisticalMechanics.Code.Percolation.ClusterDualContour
import sympy.atlas.StatisticalMechanics.Code.Percolation.DiscreteJordanSeparationFalse
import sympy.atlas.StatisticalMechanics.Code.Percolation.PcUpperUncond
import sympy.atlas.StatisticalMechanics.Code.Percolation.PcNontrivial

open Set SimpleGraph Function

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


























def djfx_DiscreteJordanSeparation' : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → ∀ {a b : Site 2},
    (∃ a' : Site 2, (faceBoundaryGraph K).Adj a a') →
    (faceBoundaryGraph K).Reachable a b →
      ∃ c : (faceBoundaryGraph K).Walk a a, c.IsCycle ∧ b ∈ c.support








theorem djfx_separation'_holds_empty {a b : Site 2}
    (hpos : ∃ a' : Site 2, (faceBoundaryGraph (∅ : Set (Site 2))).Adj a a')
    (_hreach : (faceBoundaryGraph (∅ : Set (Site 2))).Reachable a b) :
    ∃ c : (faceBoundaryGraph (∅ : Set (Site 2))).Walk a a, c.IsCycle ∧ b ∈ c.support := by
  obtain ⟨a', hadj⟩ := hpos
  exact absurd hadj (djsf_faceBoundaryGraph_empty_not_adj a a')






















theorem djfx_faceBoundaryGraph_edgeCycle (K : Set (Site 2)) (hK : K.Finite) {v w : Site 2}
    (hadj : (faceBoundaryGraph K).Adj v w) :
    ∃ c : (faceBoundaryGraph K).Walk v v, c.IsCycle ∧ w ∈ c.support := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph K hK
  obtain ⟨u, p, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph K) T hT (degree_faceBoundaryGraph_even K) hadj
  have hv : v ∈ p.support := p.fst_mem_support_of_mem_edges hedge
  have hw : w ∈ p.support := p.snd_mem_support_of_mem_edges hedge
  exact ⟨p.rotate v hv, hcyc.rotate hv, (Walk.mem_support_rotate_iff p v hv).mpr hw⟩







theorem djfx_edgeCycle_self (K : Set (Site 2)) (hK : K.Finite) {v w : Site 2}
    (hadj : (faceBoundaryGraph K).Adj v w) :
    ∃ c : (faceBoundaryGraph K).Walk v v, c.IsCycle ∧ v ∈ c.support := by
  obtain ⟨c, hcyc, _⟩ := djfx_faceBoundaryGraph_edgeCycle K hK hadj
  exact ⟨c, hcyc, c.start_mem_support⟩
















theorem djfx_exitFaceUp_edge_endpoint (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ a' : Site 2,
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj (exitFaceUp (ω := ω) hfin) a' :=
  ⟨exitFaceDown (ω := ω) hfin, exitFaces_faceBoundaryGraph_adj (ω := ω) hfin⟩










theorem djfx_enclosingContourLinksExits_of_sep' (hsep : djfx_DiscreteJordanSeparation')
    (hfin : (cluster 2 ω (origin 2)).Finite) (hsame : ExitDartsSameOrbit ω hfin) :
    EnclosingContourLinksExits ω hfin := by
  
  have hreach :
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
        (exitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) :=
    exitFaces_reachable_of_sameOrbit (ω := ω) hfin hsame
  
  have hadjLeft :
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
        (leftExitFaceDown (ω := ω) hfin) (leftExitFaceUp (ω := ω) hfin) :=
    ((leftExitFaces_faceBoundaryGraph_adj (ω := ω) hfin).symm).reachable
  have hreachUp :
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
        (exitFaceUp (ω := ω) hfin) (leftExitFaceUp (ω := ω) hfin) :=
    hreach.trans hadjLeft
  
  obtain ⟨c, hcyc, hmem⟩ :=
    hsep (cluster 2 ω (origin 2)) hfin (djfx_exitFaceUp_edge_endpoint (ω := ω) hfin) hreachUp
  exact ⟨c, hcyc, hmem⟩







theorem djfx_pcAnchoredEnclosure_of_sep' (hsep : djfx_DiscreteJordanSeparation')
    (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        ExitDartsSameOrbit ω hfin) :
    PcAnchoredEnclosure :=
  StatMech.Lattice.pcAnchoredEnclosure_of_enclosingContourLinksExits
    (fun ω hfin => djfx_enclosingContourLinksExits_of_sep' (ω := ω) hsep hfin (hsame ω hfin))












theorem djfx_pc_lt_one (hsep : djfx_DiscreteJordanSeparation')
    (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        ExitDartsSameOrbit ω hfin) :
    pc 2 < 1 :=
  pc_lt_one_of_enclosure (djfx_pcAnchoredEnclosure_of_sep' hsep hsame)













theorem djfx_pc_pos_and_lt_one (hsep : djfx_DiscreteJordanSeparation')
    (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        ExitDartsSameOrbit ω hfin) :
    0 < pc 2 ∧ pc 2 < 1 :=
  ⟨pc_pos (by norm_num), djfx_pc_lt_one hsep hsame⟩















































end Percolation

end StatMech
