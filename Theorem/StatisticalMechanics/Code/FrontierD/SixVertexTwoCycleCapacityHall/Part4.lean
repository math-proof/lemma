/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoCycleCapacityHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairedBranchResidualHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem twoCycleKeyCapacityHall_of_injectiveKeyRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hrouting : SixVertexHorizontalTwoCycleInjectiveKeyRoutings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨route, hinjective, hsupported, hcapacity⟩ := hrouting grade
  exact finiteKeyCapacityHall_of_injectiveRouting
    (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
      hmiddle_pos hmiddle_lt grade)
    SixVertexPairFineUnionKeyTwoCycleRelated route hinjective
    hsupported hcapacity

theorem twoCycleKeyCapacityHall_of_transports
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (htransports : SixVertexHorizontalTwoCycleKeyCapacityTransports T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨transport⟩ := htransports grade
  exact transport.hall


theorem actualDeficitTokenHall_of_twoCycleKeyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalActualDeficitTokenHall T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
      (sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
        hmiddle_pos hmiddle_lt) := by
  intro grade
  apply finiteRelationHall_of_keyCapacity
    sixVertexHorizontalActualDeficitFineUnionKey
    sixVertexHorizontalActualSurplusFineUnionKey
    SixVertexPairFineUnionKeyTwoCycleRelated
    (sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade)
  · intro source target hrelated
    change SixVertexConfigurationPairTwoCycleFineRelated
      (sixVertexHorizontalActualDeficitConfigurationPair source).1
      (sixVertexHorizontalActualSurplusConfigurationPair target).1
    exact sixVertexPairFineUnionKeyTwoCycleRelated_sound hrelated
  · exact hcapacity grade

theorem offDiagonalTwoCycleMatching_of_keyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt :=
  (actualDeficitTokenHall_iff_supportedMatching T
    (sixVertexHorizontalLowerSector middle hmiddle_pos)
    (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
    (sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt)).mp
    (actualDeficitTokenHall_of_twoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt hcapacity)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt
      (offDiagonalTwoCycleMatching_of_keyCapacityHall T middle
        hmiddle_pos hmiddle_lt hcapacity)

theorem sixVertexSectorTrace_logConcave_of_keyCapacityHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hcapacity : SixVertexHorizontalTwoCycleKeyCapacityHall T middle
      hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching
    T middle hmiddle_pos hmiddle_lt hc
      (offDiagonalTwoCycleMatching_of_keyCapacityHall T middle
        hmiddle_pos hmiddle_lt hcapacity)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityTransports
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (htransports : SixVertexHorizontalTwoCycleKeyCapacityTransports T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityHall
    T middle hmiddle_pos hmiddle_lt
      (twoCycleKeyCapacityHall_of_transports T middle
        hmiddle_pos hmiddle_lt htransports)

theorem sixVertexSectorTrace_logConcave_of_keyCapacityTransports
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (htransports : SixVertexHorizontalTwoCycleKeyCapacityTransports T middle
      hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_keyCapacityHall
    T middle hmiddle_pos hmiddle_lt hc
      (twoCycleKeyCapacityHall_of_transports T middle
        hmiddle_pos hmiddle_lt htransports)

end
end StatMech.FrontierD
