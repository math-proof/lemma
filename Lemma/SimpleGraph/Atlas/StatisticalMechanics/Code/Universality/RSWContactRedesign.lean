import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Universality.RSWContactRedesign.Part2
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_outerExitGoodContactPair_of_traceSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactRedesign.lean)
-/
@[path]
private lemma rlc_outerExitGoodContactPair_of_traceSeparation_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hsep : RlcOuterExitTraceSeparation G hn hlt omega)
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  Nonempty (RlcOuterExitGoodContactPair G omega) := by
-- proof
  apply StatMech.Universality.rlc_outerExitGoodContactPair_of_traceSeparation G hn hlt omega hsep horder

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_traceSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactRedesign.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_traceSeparation_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hsep : RlcOuterExitTraceSeparation G hn hlt omega)
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_traceSeparation G hn hlt omega hsep horder


-- created on 2026-10-23
