import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
open Finset SimpleGraph StatMech StatMech.Ising


/--
[closedDualWalkParity_to_boundsRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean)
-/
@[path]
private lemma closedDualWalkParity_to_boundsRegion_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hG : Gp.Preconnected)
  (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
  (hlink : ClosedDualWalkParity Gp Gd ψ) :
-- imply
  DualWalkBoundsRegion Gp Gd ψ := by
-- proof
  apply StatMech.Ising.closedDualWalkParity_to_boundsRegion hG ψ hsymm hlink

/--
[dualWalkBoundsRegion_iff_closedDualWalkParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean)
-/
@[path]
private lemma dualWalkBoundsRegion_iff_closedDualWalkParity_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hG : Gp.Preconnected)
  (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset) :
-- imply
  DualWalkBoundsRegion Gp Gd ψ ↔ ClosedDualWalkParity Gp Gd ψ := by
-- proof
  apply StatMech.Ising.dualWalkBoundsRegion_iff_closedDualWalkParity hG ψ hsymm

/--
[crossEdge_pullback_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean)
-/
@[path]
private lemma crossEdge_pullback_iff_eq
  {Gd : SimpleGraph (Site 2)}
  {w : Site 2}
  {W : Gd.Walk w w}
  {u v : Site 2} :
-- imply
  s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ crossEdge s(u, v) ∈ W.edges := by
-- proof
  apply StatMech.Ising.crossEdge_pullback_iff W u v

/--
[latticeSide_boundsRegion_of_pullback_eq_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean)
-/
@[path]
private lemma latticeSide_boundsRegion_of_pullback_eq_bdEdge_eq
  {Gd : SimpleGraph (Site 2)}
  [DecidableRel Gd.Adj]
  {S : Set (Site 2)}
  {w : Site 2}
  {W : Gd.Walk w w}
-- given
  (hpull : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge S s(u, v))) :
-- imply
  ∃ S' : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ S' u ≠ S' v) := by
-- proof
  apply StatMech.Ising.latticeSide_boundsRegion_of_pullback_eq_bdEdge S W hpull

/--
[dualWalkBoundsRegion_lattice_of_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean)
-/
@[path]
private lemma dualWalkBoundsRegion_lattice_of_bdEdgeMatch_eq
  {Gd : SimpleGraph (Site 2)}
  [DecidableRel Gd.Adj]
-- given
  (hbridge : LatticeDualWalkHasBdEdgeRegion Gd) :
-- imply
  DualWalkBoundsRegion (hypercubicLattice 2) Gd crossEdge := by
-- proof
  apply StatMech.Ising.dualWalkBoundsRegion_lattice_of_bdEdgeMatch hbridge

/--
[latticeDualWalkHasBdEdgeRegion_of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean)
-/
@[path]
private lemma latticeDualWalkHasBdEdgeRegion_of_edgeless_eq
  {Gd : SimpleGraph (Site 2)}
  [DecidableRel Gd.Adj]
-- given
  (hGd : Gd.edgeSet = ∅) :
-- imply
  LatticeDualWalkHasBdEdgeRegion Gd := by
-- proof
  apply StatMech.Ising.latticeDualWalkHasBdEdgeRegion_of_edgeless hGd

/--
[latticeDualWalkHasBdEdgeRegion_of_leftRegionMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean)
-/
@[path]
private lemma latticeDualWalkHasBdEdgeRegion_of_leftRegionMatch_eq
  {Gd : SimpleGraph (Site 2)}
  [DecidableRel Gd.Adj]
-- given
  (hmatch : ∀ {w : Site 2} (W : Gd.Walk w w), DualWalkLeftRegionMatch W) :
-- imply
  LatticeDualWalkHasBdEdgeRegion Gd := by
-- proof
  apply StatMech.Ising.latticeDualWalkHasBdEdgeRegion_of_leftRegionMatch hmatch

/--
[leftRegion_bdEdge_forces_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean)
-/
@[path]
private lemma leftRegion_bdEdge_forces_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Ising.leftRegion_bdEdge_forces_support Vc hadj hbd


-- created on 2026-10-23
