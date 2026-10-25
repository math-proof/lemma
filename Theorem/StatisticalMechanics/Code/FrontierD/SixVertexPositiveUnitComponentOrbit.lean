/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit
open Finset
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentOrbitBase

variable {T : EvenTorus} {middle : Fin (T.width + 1)} {k : Nat}


theorem negativeComponents_card
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    (base.negativeComponents positive).card = 2 * k - cardinality := by
  rw [negativeComponents, Finset.card_compl, positive.2,
    base.component_card]

theorem mask_full
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    SixVertexFullDisagreementMask base.first base.second
      (base.mask positive) :=
  sixVertexDisagreementComponentSetMask_full base.first base.second _

theorem mask_seamTransfer
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat}
    (positive : BooleanLayer
      (SixVertexDisagreementComponent base.first base.second) cardinality) :
    sixVertexTorusMaskSeamTransfer (base.mask positive)
        base.first base.second = ((2 * k - cardinality : Nat) : Int) := by
  rw [mask, sixVertexDisagreementComponentSetMask_seamTransfer_of_unit
    base.first base.second base.component_charge,
    base.negativeComponents_card]


theorem mask_injective
    (base : SixVertexPositiveUnitComponentOrbitBase T middle k)
    {cardinality : Nat} :
    Function.Injective (base.mask (cardinality := cardinality)) := by
  intro first second hmasks
  apply Subtype.ext
  apply compl_injective
  apply sixVertexDisagreementComponentSetMask_injective
    base.first base.second
  exact hmasks


end SixVertexPositiveUnitComponentOrbitBase
end
end StatMech.FrontierD
