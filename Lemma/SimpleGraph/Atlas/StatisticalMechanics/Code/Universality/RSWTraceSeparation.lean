import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWTraceSeparation.Part3
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_tracePreimageRegionSplit_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean)
-/
@[path]
private lemma rlc_tracePreimageRegionSplit_of_failure_eq
  {n a b c d : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {tau : RlcCrossingPath a b c d}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hsplit : RlcTracePreimagesSplit tau gamma gamma') :
-- imply
  RlcTracePreimageRegionSplit tau (rlc_mixedWiredReachSet G omega) := by
-- proof
  apply StatMech.Universality.rlc_tracePreimageRegionSplit_of_failure G omega hno tau hsplit

/--
[rlc_traceStraddlesLoop_of_preimageRegionSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean)
-/
@[path]
private lemma rlc_traceStraddlesLoop_of_preimageRegionSplit_eq
  {a b c d : ℤ}
  {u : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
  {gamma : RlcCrossingPath a b c d}
  {K : Set (Site 2)}
-- given
  (hregion : rlc_reflectedPrimalRegion K = jec_leftRegion C)
  (hsplit : RlcTracePreimageRegionSplit gamma K) :
-- imply
  rlc_TraceStraddlesLoop C gamma := by
-- proof
  apply StatMech.Universality.rlc_traceStraddlesLoop_of_preimageRegionSplit C gamma K hregion hsplit

/--
[rlc_traceStraddlesLoop_iff_preimageRegionSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean)
-/
@[path]
private lemma rlc_traceStraddlesLoop_iff_preimageRegionSplit_eq
  {a b c d : ℤ}
  {u : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
  {gamma : RlcCrossingPath a b c d}
  {K : Set (Site 2)}
-- given
  (hregion : rlc_reflectedPrimalRegion K = jec_leftRegion C) :
-- imply
  rlc_TraceStraddlesLoop C gamma ↔ RlcTracePreimageRegionSplit gamma K := by
-- proof
  apply StatMech.Universality.rlc_traceStraddlesLoop_iff_preimageRegionSplit C gamma K hregion

/--
[rlc_outerExitTraceSeparation_iff_windingSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean)
-/
@[path]
private lemma rlc_outerExitTraceSeparation_iff_windingSplit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  RlcOuterExitTraceSeparation G hn hlt omega ↔ RlcOuterExitTraceWindingSplit G omega := by
-- proof
  apply StatMech.Universality.rlc_outerExitTraceSeparation_iff_windingSplit G hn hlt omega

/--
[rlc_tracePreimageWindingSplit_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean)
-/
@[path]
private lemma rlc_tracePreimageWindingSplit_of_failure_eq
  {n a b c d : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {tau : RlcCrossingPath a b c d}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hJordan : RlcOuterExitJordanTraceSides G omega)
  (hsplit : RlcTracePreimagesSplit tau gamma gamma') :
-- imply
  RlcTracePreimageRegionSplit tau (rlc_outerExitWindingRegion G omega) := by
-- proof
  apply StatMech.Universality.rlc_tracePreimageWindingSplit_of_failure G omega hno hJordan tau hsplit

/--
[rlc_outerExitJordanTraceSides_of_region_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean)
-/
@[path]
private lemma rlc_outerExitJordanTraceSides_of_region_eq_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hregion : rlc_mixedWiredReachSet G omega = rlc_outerExitWindingRegion G omega) :
-- imply
  RlcOuterExitJordanTraceSides G omega := by
-- proof
  apply StatMech.Universality.rlc_outerExitJordanTraceSides_of_region_eq G omega hregion

/--
[rlc_outerExitTraceSeparation_of_failure_of_preimageSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean)
-/
@[path]
private lemma rlc_outerExitTraceSeparation_of_failure_of_preimageSplit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (htrace : RlcLowestHighestTracePreimageSplit gamma gamma')
  (hJordan : RlcOuterExitJordanTraceSides G omega) :
-- imply
  RlcOuterExitTraceSeparation G hn hlt omega := by
-- proof
  apply StatMech.Universality.rlc_outerExitTraceSeparation_of_failure_of_preimageSplit G hn hlt omega hno htrace hJordan

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_failure_of_preimageSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparation.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_failure_of_preimageSplit_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (htrace : RlcLowestHighestTracePreimageSplit gamma gamma')
  (hJordan : RlcOuterExitJordanTraceSides G omega)
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_failure_of_preimageSplit G hn hlt omega hno htrace hJordan horder


-- created on 2026-10-23
