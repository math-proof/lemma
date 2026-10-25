import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[crc2_boxBarrier_adj_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_boxBarrier_adj_of_interior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g : Site 2}
-- given
  (hfb : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
  (hint : crc2_IsBoxInteriorEdge n f g) :
-- imply
  (pmd_boxFaceBarrier ω n).Adj f g := by
-- proof
  apply StatMech.Universality.crc2_boxBarrier_adj_of_interior ω n hfb hint

/--
[crc2_walk_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_walk_lift_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {u v : Site 2}
  {w : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u v}
-- given
  (hint : ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g) :
-- imply
  (pmd_boxFaceBarrier ω n).Reachable u v := by
-- proof
  apply StatMech.Universality.crc2_walk_lift ω n w hint

/--
[crc2_frontier_down_edge_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_frontier_down_edge_interior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c r : ℤ}
-- given
  (hr0 : 0 ≤ r)
  (hrn : r ≤ n)
  (htr : mbc_IsRightFrontier ω n c r) :
-- imply
  crc2_IsBoxInteriorEdge n ![c, r] ![c, r - 1] := by
-- proof
  apply StatMech.Universality.crc2_frontier_down_edge_interior ω n hr0 hrn htr

/--
[crc2_frontierReachesBottom_of_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_frontierReachesBottom_of_arc_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (harc : crc2_FrontierArcReaches ω n) :
-- imply
  ccc_FrontierReachesBottom ω n := by
-- proof
  apply StatMech.Universality.crc2_frontierReachesBottom_of_arc ω n hn hnoH harc

/--
[crc2_arc_of_atom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_arc_of_atom_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (h : ccc_FrontierReachesBottom ω n) :
-- imply
  crc2_FrontierArcReaches ω n := by
-- proof
  apply StatMech.Universality.crc2_arc_of_atom ω n hn h

/--
[crc2_circuit_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_circuit_exists_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hc0 : 0 ≤ c)
  (hcn : c ≤ n) :
-- imply
  ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), cyc.IsCycle := by
-- proof
  apply StatMech.Universality.crc2_circuit_exists ω hn hnoH hc0 hcn

/--
[crc2_barrierConnectsRows_of_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_barrierConnectsRows_of_arc_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (harc : crc2_FrontierArcReaches ω n) :
-- imply
  pmd_BarrierConnectsRows ω n := by
-- proof
  apply StatMech.Universality.crc2_barrierConnectsRows_of_arc ω n hn hnoH harc

/--
[crc2_faceDualVCrossing_of_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_faceDualVCrossing_of_arc_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (harc : crc2_FrontierArcReaches ω n) :
-- imply
  pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.crc2_faceDualVCrossing_of_arc ω n hn hnoH harc

/--
[crc2_exhaustivity_of_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_exhaustivity_of_arc_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (harc : crc2_FrontierArcReaches ω n) :
-- imply
  HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.crc2_exhaustivity_of_arc ω n hn hnoH harc

/--
[crc2_wall_down_edge_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_wall_down_edge_interior_eq
  {r : ℤ}
-- given
  (hr0 : 0 ≤ r)
  (hr2 : r ≤ 2) :
-- imply
  crc2_IsBoxInteriorEdge 2 ![0, r] ![0, r - 1] := by
-- proof
  apply StatMech.Universality.crc2_wall_down_edge_interior hr0 hr2

/--
[crc2_wall_frontierArcReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_wall_frontierArcReaches_eq :
-- imply
  crc2_FrontierArcReaches bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.crc2_wall_frontierArcReaches

/--
[crc2_wall_atom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_wall_atom_eq :
-- imply
  ccc_FrontierReachesBottom bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.crc2_wall_atom

/--
[crc2_wall_faceDualVCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_wall_faceDualVCrossing_eq :
-- imply
  pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.crc2_wall_faceDualVCrossing

/--
[crc2_wall_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean)
-/
@[path]
private lemma crc2_wall_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.crc2_wall_noH


-- created on 2026-10-23
