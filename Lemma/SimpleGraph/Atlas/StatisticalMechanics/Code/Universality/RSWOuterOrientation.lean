import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWOuterOrientation.Part4
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_traceContactsCutOffRelaxedBadEdges_of_outerContourContactOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean)
-/
@[path]
private lemma rlc_traceContactsCutOffRelaxedBadEdges_of_outerContourContactOrder_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : RlcOrientedContourContactOrder G omega) :
-- imply
  RlcTraceContactsCutOffRelaxedBadEdges G omega (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) h.anchor) := by
-- proof
  apply StatMech.Universality.rlc_traceContactsCutOffRelaxedBadEdges_of_outerContourContactOrder G omega h

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_outerContourContactOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_outerContourContactOrder_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (h : RlcOrientedContourContactOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_outerContourContactOrder G hn hlt omega h

/--
[rlc_outerExitDart_isBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean)
-/
@[path]
private lemma rlc_outerExitDart_isBoundary_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  IsBoundaryDart (rlc_mixedWiredReachSet G omega) (rlc_outerExitDart G omega) := by
-- proof
  apply StatMech.Universality.rlc_outerExitDart_isBoundary G omega

/--
[rlc_outerExitOrbit_head_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean)
-/
@[path]
private lemma rlc_outerExitOrbit_head_reachable_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {k : ℕ} :
-- imply
  let K := rlc_mixedWiredReachSet G omega let e := rlc_outerExitDart G omega ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, (rlc_outerExitDart_isBoundary G omega).2⟩ ⟨((dartNext K)^[k] e).head, (iterate_isBoundaryDart' K e (rlc_outerExitDart_isBoundary G omega) k).2⟩ := by
-- proof
  apply StatMech.Universality.rlc_outerExitOrbit_head_reachable G omega k

/--
[rlc_outerExit_traceContactsCutOffRelaxedBadEdges_of_straddles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean)
-/
@[path]
private lemma rlc_outerExit_traceContactsCutOffRelaxedBadEdges_of_straddles_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hright : rlc_TraceStraddlesLoop ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)) gamma.1)
  (hleft : rlc_TraceStraddlesLoop ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)) gamma'.1)
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  RlcTraceContactsCutOffRelaxedBadEdges G omega (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) (rlc_outerExitAnchor G omega)) := by
-- proof
  apply StatMech.Universality.rlc_outerExit_traceContactsCutOffRelaxedBadEdges_of_straddles G hn hlt omega hright hleft horder

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_outerExit_straddles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_outerExit_straddles_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hright : rlc_TraceStraddlesLoop ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)) gamma.1)
  (hleft : rlc_TraceStraddlesLoop ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe (rlc_openSubgraph_le_lattice _)) gamma'.1)
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_outerExit_straddles G hn hlt omega hright hleft horder

/--
[rlc_traceContactsCutOffRelaxedBadEdges_of_outerExitContactOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean)
-/
@[path]
private lemma rlc_traceContactsCutOffRelaxedBadEdges_of_outerExitContactOrder_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : RlcOuterContourContactOrder G omega) :
-- imply
  RlcTraceContactsCutOffRelaxedBadEdges G omega (mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega) (rlc_outerExitAnchor G omega)) := by
-- proof
  apply StatMech.Universality.rlc_traceContactsCutOffRelaxedBadEdges_of_outerExitContactOrder G omega h

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitContactOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterOrientation.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitContactOrder_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (h : RlcOuterContourContactOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitContactOrder G hn hlt omega h


-- created on 2026-10-23
