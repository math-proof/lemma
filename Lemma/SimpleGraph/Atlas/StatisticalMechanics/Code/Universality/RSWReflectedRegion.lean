import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_leftRegion_dualReflect_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_leftRegion_dualReflect_map_eq
  {a : Site 2}
  {C : (hypercubicLattice 2).Walk a a} :
-- imply
  jec_leftRegion (C.map rlc_dualReflectLatticeHom) = rlc_reflectedPrimalRegion (jec_leftRegion C) := by
-- proof
  apply StatMech.Universality.rlc_leftRegion_dualReflect_map C

/--
[rlc_reflectedRegion_eq_leftRegion_map_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_reflectedRegion_eq_leftRegion_map_of_eq_eq
  {a : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
  {F : Set (Site 2)}
-- given
  (hF : F = jec_leftRegion C) :
-- imply
  rlc_reflectedPrimalRegion F = jec_leftRegion (C.map rlc_dualReflectLatticeHom) := by
-- proof
  apply StatMech.Universality.rlc_reflectedRegion_eq_leftRegion_map_of_eq C F hF

/--
[rlc_dualReflectOpenWalk_underlying_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_dualReflectOpenWalk_underlying_edges_eq
  {eta : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {w : (openSubgraph 2 (fci_faceDualConfig eta)).Walk x y} :
-- imply
  ((rlc_dualReflectOpenWalk eta w).mapLe (rlc_openSubgraph_le_lattice _)).edges = ((w.mapLe (rlc_openSubgraph_le_lattice _)).map rlc_dualReflectLatticeHom).edges := by
-- proof
  apply StatMech.Universality.rlc_dualReflectOpenWalk_underlying_edges eta w

/--
[rlc_outerExitReflectedOpenLoop_edges_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_outerExitReflectedOpenLoop_edges_eq_map_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  (((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)).edges) = (((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) (rlc_outerExitAnchor G omega)).mapLe (faceBoundaryGraph_le _)).map rlc_dualReflectLatticeHom).edges := by
-- proof
  apply StatMech.Universality.rlc_outerExitReflectedOpenLoop_edges_eq_map G hn hlt omega

/--
[rlc_outerExitReflectedOpenLoop_leftRegion_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_outerExitReflectedOpenLoop_leftRegion_eq_map_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  jec_leftRegion ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)) = jec_leftRegion (((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) (rlc_outerExitAnchor G omega)).mapLe (faceBoundaryGraph_le _)).map rlc_dualReflectLatticeHom) := by
-- proof
  apply StatMech.Universality.rlc_outerExitReflectedOpenLoop_leftRegion_eq_map G hn hlt omega

/--
[rlc_outerExit_reflectedRegion_eq_leftRegion_of_fill_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_outerExit_reflectedRegion_eq_leftRegion_of_fill_eq_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {F : Set (Site 2)}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hfill : F = jec_leftRegion ((mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) (rlc_outerExitAnchor G omega)).mapLe (faceBoundaryGraph_le _))) :
-- imply
  rlc_reflectedPrimalRegion F = jec_leftRegion ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)) := by
-- proof
  apply StatMech.Universality.rlc_outerExit_reflectedRegion_eq_leftRegion_of_fill_eq G hn hlt omega F hfill

/--
[rlc_right_start_mem_reflectedPrimalRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_right_start_mem_reflectedPrimalRegion_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {K : Set (Site 2)} :
-- imply
  (gamma.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K ↔ ![-(gamma.1.1 : Site 2) 0, (gamma.1.1 : Site 2) 1 - 1] ∈ K := by
-- proof
  apply StatMech.Universality.rlc_right_start_mem_reflectedPrimalRegion_iff gamma K

/--
[rlc_right_end_mem_reflectedPrimalRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_right_end_mem_reflectedPrimalRegion_iff_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {K : Set (Site 2)} :
-- imply
  (gamma.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K ↔ ![-(gamma.1.2.1 : Site 2) 0, (gamma.1.2.1 : Site 2) 1 - 1] ∈ K := by
-- proof
  apply StatMech.Universality.rlc_right_end_mem_reflectedPrimalRegion_iff gamma K

/--
[rlc_left_start_mem_reflectedPrimalRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_left_start_mem_reflectedPrimalRegion_iff_eq
  {n : ℤ}
  {gamma' : RlcLeftDiagonalPath n}
  {K : Set (Site 2)} :
-- imply
  (gamma'.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K ↔ ![-(gamma'.1.1 : Site 2) 0, (gamma'.1.1 : Site 2) 1 - 1] ∈ K := by
-- proof
  apply StatMech.Universality.rlc_left_start_mem_reflectedPrimalRegion_iff gamma' K

/--
[rlc_left_end_mem_reflectedPrimalRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_left_end_mem_reflectedPrimalRegion_iff_eq
  {n : ℤ}
  {gamma' : RlcLeftDiagonalPath n}
  {K : Set (Site 2)} :
-- imply
  (gamma'.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K ↔ ![-(gamma'.1.2.1 : Site 2) 0, (gamma'.1.2.1 : Site 2) 1 - 1] ∈ K := by
-- proof
  apply StatMech.Universality.rlc_left_end_mem_reflectedPrimalRegion_iff gamma' K

/--
[rlc_reflectedEndpointXor_iff_affine_preimages](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_reflectedEndpointXor_iff_affine_preimages_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {K : Set (Site 2)} :
-- imply
  RlcReflectedEndpointXor gamma gamma' K ↔ ((![-(gamma.1.1 : Site 2) 0, (gamma.1.1 : Site 2) 1 - 1] ∈ K) ≠ (![-(gamma.1.2.1 : Site 2) 0, (gamma.1.2.1 : Site 2) 1 - 1] ∈ K)) ∧ ((![-(gamma'.1.1 : Site 2) 0, (gamma'.1.1 : Site 2) 1 - 1] ∈ K) ≠ (![-(gamma'.1.2.1 : Site 2) 0, (gamma'.1.2.1 : Site 2) 1 - 1] ∈ K)) := by
-- proof
  apply StatMech.Universality.rlc_reflectedEndpointXor_iff_affine_preimages gamma gamma' K

/--
[rlc_reflectedEndpointXor_of_affine_preimage_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWReflectedRegion.lean)
-/
@[path]
private lemma rlc_reflectedEndpointXor_of_affine_preimage_sides_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {K : Set (Site 2)}
-- given
  (hr0 : ![-(gamma.1.1 : Site 2) 0, (gamma.1.1 : Site 2) 1 - 1] ∈ K)
  (hr1 : ![-(gamma.1.2.1 : Site 2) 0, (gamma.1.2.1 : Site 2) 1 - 1] ∉ K)
  (hl0 : ![-(gamma'.1.1 : Site 2) 0, (gamma'.1.1 : Site 2) 1 - 1] ∉ K)
  (hl1 : ![-(gamma'.1.2.1 : Site 2) 0, (gamma'.1.2.1 : Site 2) 1 - 1] ∈ K) :
-- imply
  RlcReflectedEndpointXor gamma gamma' K := by
-- proof
  apply StatMech.Universality.rlc_reflectedEndpointXor_of_affine_preimage_sides gamma gamma' K hr0 hr1 hl0 hl1


-- created on 2026-10-23
