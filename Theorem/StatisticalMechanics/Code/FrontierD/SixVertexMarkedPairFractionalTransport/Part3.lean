/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexMarkedSectorPairMass_le_of_fractionalTransport
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (transport : SixVertexMarkedPairFractionalTransport
      T lower middle upper k) :
    sixVertexMarkedSectorPairMass T lower upper k <=
      sixVertexMarkedSectorPairMass T middle middle k := by
  change
    (∑ pair : SixVertexMarkedPairSource T lower upper,
      sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k) <=
    ∑ pair : SixVertexMarkedPairTarget T middle,
      sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k
  exact transport.total_le


theorem sixVertexMarkedSectorPairMass_le_of_fractionalTransportOn
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    {related : SixVertexMarkedPairSource T lower upper ->
      SixVertexMarkedPairTarget T middle -> Prop}
    (transport : SixVertexMarkedPairFractionalTransportOn
      T lower middle upper k related) :
    sixVertexMarkedSectorPairMass T lower upper k <=
      sixVertexMarkedSectorPairMass T middle middle k :=
  sixVertexMarkedSectorPairMass_le_of_fractionalTransport
    transport.toFiniteFractionalTransport


theorem coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransport
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (transport : SixVertexMarkedPairFractionalTransport
      T lower middle upper k) :
    (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val *
        sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <=
      (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k := by
  rw [pow_two]
  rw [← sixVertexMarkedSectorPairMass_eq_coeff,
    ← sixVertexMarkedSectorPairMass_eq_coeff]
  exact sixVertexMarkedSectorPairMass_le_of_fractionalTransport transport


theorem coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransportOn
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    {related : SixVertexMarkedPairSource T lower upper ->
      SixVertexMarkedPairTarget T middle -> Prop}
    (transport : SixVertexMarkedPairFractionalTransportOn
      T lower middle upper k related) :
    (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val *
        sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <=
      (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k :=
  coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransport
    transport.toFiniteFractionalTransport

end
end StatMech.FrontierD
