import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelHallCapacity
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_twoChannelPIMSFixedPayloadCapacity_iff_nonempty_packing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelHallCapacity.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSFixedPayloadCapacity_iff_nonempty_packing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
-- imply
  RlcTwoChannelPIMSFixedPayloadCapacity hclosure ↔ Nonempty (RlcTwoChannelPIMSDiscardedPayloadPacking hclosure) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSFixedPayloadCapacity_iff_nonempty_packing hclosure


-- created on 2026-10-23
