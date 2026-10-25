/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part5


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoActiveCycleRepairSurplusCapacity_pos :
    0 < sixVertexHorizontalActualSurplusFineUnionCapacity
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveCycleRepairKey := by
  change 0 < Fintype.card
    (SixVertexHorizontalActualSurplusFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveCycleRepairKey)
  apply Fintype.card_pos_iff.mpr
  exact ⟨sixVertexFourByTwoActiveCycleRepairSurplusKeyFiber⟩

theorem sixVertexFourByTwoActiveObstructionToken_cycleRepair_supported :
    sixVertexHorizontalOffDiagonalTwoCycleSupport
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionToken
      sixVertexFourByTwoActiveCycleRepairSurplusToken := by
  change SixVertexConfigurationPairTwoCycleFineRelated
    (sixVertexHorizontalActualDeficitConfigurationPair
      sixVertexFourByTwoActiveObstructionToken).1
    (sixVertexHorizontalActualSurplusConfigurationPair
      sixVertexFourByTwoActiveCycleRepairSurplusToken).1
  rw [sixVertexFourByTwoActiveObstructionConfigurationPair_eq,
    sixVertexFourByTwoActiveCycleRepairConfigurationPair_eq]
  exact sixVertexFourByTwo_cycleMiddle_fineRelated

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveSourceIndex_eq_of_signature
    (i : Fin 4 × Fin 50) :
    ((forall v,
          ((sixVertexFourByTwoSourceIndexArrows i).1.horizontal v).toNat +
              ((sixVertexFourByTwoSourceIndexArrows i).2.horizontal v).toNat =
            (sixVertexFourByTwoLowArrows.horizontal v).toNat +
              (sixVertexFourByTwoHighArrows.horizontal v).toNat) ∧
        (forall v,
          ((sixVertexFourByTwoSourceIndexArrows i).1.vertical v).toNat +
              ((sixVertexFourByTwoSourceIndexArrows i).2.vertical v).toNat =
            (sixVertexFourByTwoLowArrows.vertical v).toNat +
              (sixVertexFourByTwoHighArrows.vertical v).toNat) ∧
        sixVertexHorizontalPairBoundedFineRowProfile
            ((sixVertexFourByTwoSourceIndexArrows i).1.horizontal,
              (sixVertexFourByTwoSourceIndexArrows i).2.horizontal) =
          sixVertexHorizontalPairBoundedFineRowProfile
            (sixVertexFourByTwoLowArrows.horizontal,
              sixVertexFourByTwoHighArrows.horizontal)) ->
      i = (0, 29) := by
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> decide +revert

theorem sixVertexFourByTwoActiveSourceIndex_eq_of_key
    (i : Fin 4 × Fin 50)
    (hkey : sixVertexPairFineUnionKey
        (sixVertexFourByTwoSourceIndexArrows i) =
      sixVertexPairFineUnionKey
        (sixVertexFourByTwoLowArrows,
          sixVertexFourByTwoHighArrows)) :
    i = (0, 29) := by
  apply sixVertexFourByTwoActiveSourceIndex_eq_of_signature i
  constructor
  · intro v
    have h := congrFun
      (congrArg SixVertexPairFineUnionKey.horizontal hkey) v
    exact congrArg Fin.val h
  · constructor
    · intro v
      have h := congrFun
        (congrArg SixVertexPairFineUnionKey.vertical hkey) v
      exact congrArg Fin.val h
    · exact congrArg SixVertexPairFineUnionKey.fine hkey

theorem sixVertexFourByTwoActiveSourceIndexArrows_eq :
    sixVertexFourByTwoSourceIndexArrows (0, 29) =
      (sixVertexFourByTwoLowArrows,
        sixVertexFourByTwoHighArrows) := by
  apply Prod.ext <;> apply SixVertexArrows.ext <;> funext v
  all_goals
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert

theorem sixVertexFourByTwoActiveSourceConfigurationPair_unique_of_key
    (source :
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorZero ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorTwo)
    (hkey : sixVertexPairFineUnionKey (source.1.1, source.2.1) =
      sixVertexPairFineUnionKey
        (sixVertexFourByTwoLowArrows,
          sixVertexFourByTwoHighArrows)) :
    source = (sixVertexFourByTwoLowConfiguration,
      sixVertexFourByTwoHighConfiguration) := by
  let i := sixVertexFourByTwoSourcePairEquiv.symm source
  have hsource := sixVertexFourByTwoSourcePairEquiv.apply_symm_apply source
  have hsourceArrows := congrArg
    (fun pair => (pair.1.1, pair.2.1)) hsource
  change sixVertexFourByTwoSourceIndexArrows i =
    (source.1.1, source.2.1) at hsourceArrows
  have hindex : i = (0, 29) := by
    apply sixVertexFourByTwoActiveSourceIndex_eq_of_key i
    rw [hsourceArrows]
    exact hkey
  calc
    source = sixVertexFourByTwoSourcePairEquiv i := hsource.symm
    _ = sixVertexFourByTwoSourcePairEquiv (0, 29) := congrArg _ hindex
    _ = (sixVertexFourByTwoLowConfiguration,
          sixVertexFourByTwoHighConfiguration) := by
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst
          sixVertexFourByTwoActiveSourceIndexArrows_eq
      · apply Subtype.ext
        exact congrArg Prod.snd
          sixVertexFourByTwoActiveSourceIndexArrows_eq

theorem sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq
    (source : SixVertexHorizontalActualDeficitFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionKey) :
    source = ⟨sixVertexFourByTwoActiveObstructionToken, rfl⟩ := by
  apply Subtype.ext
  apply sixVertexHorizontalActualDeficitConfigurationPair_injective
  apply Subtype.ext
  calc
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1 =
        (sixVertexFourByTwoLowConfiguration,
          sixVertexFourByTwoHighConfiguration) := by
      apply sixVertexFourByTwoActiveSourceConfigurationPair_unique_of_key
      exact source.2.trans
        sixVertexFourByTwoActiveObstructionKey_eq_sourceKey
    _ = (sixVertexHorizontalActualDeficitConfigurationPair
          sixVertexFourByTwoActiveObstructionToken).1 :=
      sixVertexFourByTwoActiveObstructionConfigurationPair_eq.symm

theorem sixVertexFourByTwoActiveObstructionSourceKeyFiber_subsingleton
    (first second : SixVertexHorizontalActualDeficitFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionKey) :
    first = second :=
  (sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq first).trans
    (sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq second).symm

end
end StatMech.FrontierD
