/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexMarkedSectorPairMass_le_of_switch
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (S : SixVertexGlobalMarkedPairSwitch T lower middle upper k) :
    sixVertexMarkedSectorPairMass T lower upper k <=
      sixVertexMarkedSectorPairMass T middle middle k := by
  let domain := SixVertexMarkedSectorConfiguration T lower ×
    SixVertexMarkedSectorConfiguration T upper
  let codomain := SixVertexMarkedSectorConfiguration T middle ×
    SixVertexMarkedSectorConfiguration T middle
  let w : domain -> Real := fun pair =>
    sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k
  let v : codomain -> Real := fun pair =>
    sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k
  change (∑ pair : domain, w pair) <= ∑ pair : codomain, v pair
  calc
    (∑ pair : domain, w pair) <= ∑ pair : domain, v (S.toPair pair) :=
      Finset.sum_le_sum fun pair hpair => S.multiplicity_le pair
    _ = ∑ pair ∈ Finset.univ.image S.toPair, v pair := by
      rw [Finset.sum_image]
      exact S.injective.injOn
    _ <= ∑ pair ∈ (Finset.univ : Finset codomain), v pair := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr fun pair hpair => Finset.mem_univ _
      · intro pair hpair hall
        exact sixVertexMarkedPairMultiplicity_nonneg
          pair.1.1 pair.2.1 pair.1.2.1 pair.2.2.1 k
    _ = ∑ pair : codomain, v pair := by simp


theorem coeff_shiftedSectorTrace_mul_le_sq_of_globalMarkedPairSwitch
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (S : SixVertexGlobalMarkedPairSwitch T lower middle upper k) :
    (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val *
        sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <=
      (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k := by
  rw [pow_two]
  rw [← sixVertexMarkedSectorPairMass_eq_coeff,
    ← sixVertexMarkedSectorPairMass_eq_coeff]
  exact sixVertexMarkedSectorPairMass_le_of_switch S

end
end StatMech.FrontierD
