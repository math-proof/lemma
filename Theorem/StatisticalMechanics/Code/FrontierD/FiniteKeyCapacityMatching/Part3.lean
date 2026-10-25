/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem twoCycleExpandedCapacityMatchings_of_offDiagonalMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hmatching : SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
      hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨matching, hinjective, hsupported⟩ := hmatching grade
  have hcopies := finiteKeyExpandedMatching_of_supportedMatching
    (sixVertexHorizontalActualDeficitFineUnionKey
      (T := T) (grade := grade))
    (sixVertexHorizontalActualSurplusFineUnionKey
      (T := T) (grade := grade))
    SixVertexPairFineUnionKeyTwoCycleRelated matching hinjective (by
      intro source
      apply sixVertexPairFineUnionKeyTwoCycleRelated_complete
      have h := hsupported source
      change SixVertexConfigurationPairTwoCycleFineRelated
        (sixVertexHorizontalActualDeficitConfigurationPair source).1
        (sixVertexHorizontalActualSurplusConfigurationPair
          (matching source)).1 at h
      exact h)
  simpa only [sixVertexHorizontalActualDeficitFineUnionCapacity,
    sixVertexHorizontalActualSurplusFineUnionCapacity] using hcopies


theorem twoCycleKeyCapacityHall_iff_expandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexHorizontalTwoCycleKeyCapacityHall T middle
        hmiddle_pos hmiddle_lt <->
      SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
        hmiddle_pos hmiddle_lt := by
  classical
  unfold SixVertexHorizontalTwoCycleKeyCapacityHall
    SixVertexHorizontalTwoCycleExpandedCapacityMatchings
  constructor
  · intro hcapacity grade
    exact (finiteKeyCapacityHall_iff_exists_expandedMatching
      (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade)
      (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade)
      SixVertexPairFineUnionKeyTwoCycleRelated).mp (hcapacity grade)
  · intro hmatching grade
    exact (finiteKeyCapacityHall_iff_exists_expandedMatching
      (sixVertexHorizontalActualDeficitFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade)
      (sixVertexHorizontalActualSurplusFineUnionCapacity T middle
        hmiddle_pos hmiddle_lt grade)
      SixVertexPairFineUnionKeyTwoCycleRelated).mpr (hmatching grade)


theorem offDiagonalTwoCycleMatching_iff_expandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    SixVertexHorizontalOffDiagonalTwoCycleMatching T middle
        hmiddle_pos hmiddle_lt <->
      SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
        hmiddle_pos hmiddle_lt := by
  constructor
  · exact twoCycleExpandedCapacityMatchings_of_offDiagonalMatching
      T middle hmiddle_pos hmiddle_lt
  · intro hmatching
    apply offDiagonalTwoCycleMatching_of_keyCapacityHall
    exact (twoCycleKeyCapacityHall_iff_expandedCapacityMatchings
      T middle hmiddle_pos hmiddle_lt).mpr hmatching

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_expandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hmatching : SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_keyCapacityHall
    T middle hmiddle_pos hmiddle_lt
      ((twoCycleKeyCapacityHall_iff_expandedCapacityMatchings
        T middle hmiddle_pos hmiddle_lt).mpr hmatching)

theorem sixVertexSectorTrace_logConcave_of_expandedCapacityMatchings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hmatching : SixVertexHorizontalTwoCycleExpandedCapacityMatchings T middle
      hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_keyCapacityHall
    T middle hmiddle_pos hmiddle_lt hc
      ((twoCycleKeyCapacityHall_iff_expandedCapacityMatchings
        T middle hmiddle_pos hmiddle_lt).mpr hmatching)

end
end StatMech.FrontierD
