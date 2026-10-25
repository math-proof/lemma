import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWRayTransport.Part5
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_oppositeLoopSides_iff_leftRegion_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_oppositeLoopSides_iff_leftRegion_xor_eq
  {a : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
  {x y : Site 2} :
-- imply
  rlc_OppositeLoopSides C x y ↔ (x ∈ jec_leftRegion C ∧ y ∉ jec_leftRegion C) ∨ (x ∉ jec_leftRegion C ∧ y ∈ jec_leftRegion C) := by
-- proof
  apply StatMech.Universality.rlc_oppositeLoopSides_iff_leftRegion_xor C x y

/--
[rlc_not_oppositeLoopSides_of_both_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_not_oppositeLoopSides_of_both_mem_leftRegion_eq
  {a : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∈ jec_leftRegion C)
  (hy : y ∈ jec_leftRegion C) :
-- imply
  ¬ rlc_OppositeLoopSides C x y := by
-- proof
  apply StatMech.Universality.rlc_not_oppositeLoopSides_of_both_mem_leftRegion C hx hy

/--
[rlc_not_oppositeLoopSides_of_both_not_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_not_oppositeLoopSides_of_both_not_mem_leftRegion_eq
  {a : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∉ jec_leftRegion C)
  (hy : y ∉ jec_leftRegion C) :
-- imply
  ¬ rlc_OppositeLoopSides C x y := by
-- proof
  apply StatMech.Universality.rlc_not_oppositeLoopSides_of_both_not_mem_leftRegion C hx hy

/--
[rlc_primalDualReflect_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_primalDualReflect_zero_eq
  {x : Site 2} :
-- imply
  rlc_primalDualReflect x 0 = -x 0 := by
-- proof
  apply StatMech.Universality.rlc_primalDualReflect_zero x

/--
[rlc_primalDualReflect_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_primalDualReflect_one_eq
  {x : Site 2} :
-- imply
  rlc_primalDualReflect x 1 = x 1 + 1 := by
-- proof
  apply StatMech.Universality.rlc_primalDualReflect_one x

/--
[rlc_primalDualReflect_symm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_primalDualReflect_symm_zero_eq
  {x : Site 2} :
-- imply
  rlc_primalDualReflect.symm x 0 = -x 0 := by
-- proof
  apply StatMech.Universality.rlc_primalDualReflect_symm_zero x

/--
[rlc_primalDualReflect_symm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_primalDualReflect_symm_one_eq
  {x : Site 2} :
-- imply
  rlc_primalDualReflect.symm x 1 = x 1 - 1 := by
-- proof
  apply StatMech.Universality.rlc_primalDualReflect_symm_one x

/--
[rlc_rayEdge_dualReflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_rayEdge_dualReflect_iff_eq
  {z u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  jec_rayEdge (rlc_primalDualReflect z) s(rlc_dualReflect u, rlc_dualReflect v) ↔ bdEdge (jec_belowSet (z 1)) s(u, v) ∧ ¬ jec_rayEdge z s(u, v) := by
-- proof
  apply StatMech.Universality.rlc_rayEdge_dualReflect_iff hadj

/--
[rlc_rayParity_dualReflect_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_rayParity_dualReflect_map_eq
  {a : Site 2}
  {w : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  Even (jec_rayCount (rlc_primalDualReflect z) (w.map rlc_dualReflectLatticeHom)) ↔ Even (jec_rayCount z w) := by
-- proof
  apply StatMech.Universality.rlc_rayParity_dualReflect_map w z

/--
[rlc_mem_reflectedPrimalRegion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_mem_reflectedPrimalRegion_iff_eq
  {K : Set (Site 2)}
  {x : Site 2} :
-- imply
  x ∈ rlc_reflectedPrimalRegion K ↔ rlc_primalDualReflect.symm x ∈ K := by
-- proof
  apply StatMech.Universality.rlc_mem_reflectedPrimalRegion_iff K x

/--
[rlc_endpointSides_of_reflectedRegion_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_endpointSides_of_reflectedRegion_xor_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {a : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
  {K : Set (Site 2)}
-- given
  (hregion : rlc_reflectedPrimalRegion K = jec_leftRegion C)
  (hxor : RlcReflectedEndpointXor gamma gamma' K) :
-- imply
  rlc_OppositeLoopSides C (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2) ∧ rlc_OppositeLoopSides C (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_endpointSides_of_reflectedRegion_xor C K hregion hxor

/--
[rlc_outerExitEndpointSides_of_reflectedRegion_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_outerExitEndpointSides_of_reflectedRegion_xor_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hregion : rlc_reflectedPrimalRegion (rlc_mixedWiredReachSet G omega) = jec_leftRegion ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)))
  (hxor : RlcReflectedEndpointXor gamma gamma' (rlc_mixedWiredReachSet G omega)) :
-- imply
  RlcOuterExitEndpointSides G hn hlt omega := by
-- proof
  apply StatMech.Universality.rlc_outerExitEndpointSides_of_reflectedRegion_xor G hn hlt omega hregion hxor

/--
[rlc_outerExitGoodContactPair_of_endpointSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_outerExitGoodContactPair_of_endpointSides_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hsides : RlcOuterExitEndpointSides G hn hlt omega)
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  Nonempty (RlcOuterExitGoodContactPair G omega) := by
-- proof
  apply StatMech.Universality.rlc_outerExitGoodContactPair_of_endpointSides G hn hlt omega hsides horder

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_reflectedRegion_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_reflectedRegion_xor_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hregion : rlc_reflectedPrimalRegion (rlc_mixedWiredReachSet G omega) = jec_leftRegion ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)))
  (hxor : RlcReflectedEndpointXor gamma gamma' (rlc_mixedWiredReachSet G omega))
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_reflectedRegion_xor G hn hlt omega hregion hxor horder

/--
[rlc_not_outerExitEndpointSides_of_failure_of_directRegionEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean)
-/
@[path]
private lemma rlc_not_outerExitEndpointSides_of_failure_of_directRegionEq_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hregion : rlc_mixedWiredReachSet G omega = jec_leftRegion ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _))) :
-- imply
  ¬ RlcOuterExitEndpointSides G hn hlt omega := by
-- proof
  apply StatMech.Universality.rlc_not_outerExitEndpointSides_of_failure_of_directRegionEq G hn hlt omega hno hregion


-- created on 2026-10-23
