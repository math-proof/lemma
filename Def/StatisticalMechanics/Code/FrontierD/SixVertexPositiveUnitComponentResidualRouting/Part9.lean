/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part3


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexHorizontalResidualGeometricSurplusRepair

noncomputable def ofCertificateSourceWeightZero
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (certificate : SixVertexHorizontalResidualGeometricCertificate
      (sixVertexHorizontalHallSourceCanonicalLoop source))
    (hzero : sixVertexHorizontalPairProfileChooseWeight
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      (sixVertexHorizontalPairCompletionProfile T
        (certificate.loopTarget.1.1.1.1.horizontal,
          certificate.loopTarget.1.1.2.1.horizontal)) = 0) :
    SixVertexHorizontalResidualGeometricSurplusRepair source := by
  let configuration :
      {pair : SixVertexMarkedSectorConfiguration T middle ×
          SixVertexMarkedSectorConfiguration T middle //
        sixVertexConfigurationPairBigrade pair = grade} :=
    ⟨certificate.loopTarget.1.1, by
      rw [← sixVertexLoopDecoratedPairBigrade_eq_configurationPair]
      exact certificate.loopTarget.2⟩
  have hrange :=
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
      configuration hzero
  let target := Classical.choose hrange
  have htarget := Classical.choose_spec hrange
  exact
    { certificate := certificate
      target := target
      target_physical := congrArg Subtype.val htarget }


noncomputable def ofCertificateLeftIncompatible
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (certificate : SixVertexHorizontalResidualGeometricCertificate
      (sixVertexHorizontalHallSourceCanonicalLoop source))
    (hleft : IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      certificate.loopTarget.1.1.1.1.horizontal)) :
    SixVertexHorizontalResidualGeometricSurplusRepair source :=
  ofCertificateSourceWeightZero source certificate
    (sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      (certificate.loopTarget.1.1.1.1.horizontal,
        certificate.loopTarget.1.1.2.1.horizontal) hleft)


noncomputable def ofCertificateRightIncompatible
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (certificate : SixVertexHorizontalResidualGeometricCertificate
      (sixVertexHorizontalHallSourceCanonicalLoop source))
    (hright : IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      certificate.loopTarget.1.1.2.1.horizontal)) :
    SixVertexHorizontalResidualGeometricSurplusRepair source :=
  ofCertificateSourceWeightZero source certificate
    (sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_right_isEmpty
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      (certificate.loopTarget.1.1.1.1.horizontal,
        certificate.loopTarget.1.1.2.1.horizontal) hright)


noncomputable def ofUnitStrandIncompatible
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (hdegree : SixVertexLocallyDegreeTwo
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.1.1
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.2.1)
    (seed : SixVertexOrientedDisagreementDart
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.1.1
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.1.2.1
      (sixVertexHorizontalHallSourceCanonicalLoop source).1.1.2.2.1
      hdegree seed).sum = 1)
    (hincompatible :
      let certificate :=
        SixVertexHorizontalResidualGeometricCertificate.ofUnitStrand
          hdegree seed hunit
      IsEmpty (SixVertexHorizontalSectorCompletion T
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          certificate.loopTarget.1.1.1.1.horizontal) ∨
        IsEmpty (SixVertexHorizontalSectorCompletion T
          (sixVertexHorizontalUpperSector middle hmiddle_lt)
          certificate.loopTarget.1.1.2.1.horizontal)) :
    SixVertexHorizontalResidualGeometricSurplusRepair source := by
  let certificate :=
    SixVertexHorizontalResidualGeometricCertificate.ofUnitStrand
      hdegree seed hunit
  change IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      certificate.loopTarget.1.1.1.1.horizontal) ∨
    IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalUpperSector middle hmiddle_lt)
      certificate.loopTarget.1.1.2.1.horizontal) at hincompatible
  by_cases hleft : IsEmpty (SixVertexHorizontalSectorCompletion T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      certificate.loopTarget.1.1.1.1.horizontal)
  · exact ofCertificateLeftIncompatible source certificate hleft
  · exact ofCertificateRightIncompatible source certificate
      (hincompatible.resolve_left hleft)


noncomputable def ofFineRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade)
    (related : sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source target) :
    SixVertexHorizontalResidualGeometricSurplusRepair source where
  certificate := .fineRelated
    (sixVertexHorizontalHallTargetCanonicalLoop target)
    (by
      change SixVertexConfigurationPairTwoCycleFineRelated
        (sixVertexHorizontalActualDeficitConfigurationPair source).1
        (sixVertexHorizontalActualSurplusConfigurationPair target).1
      exact related)
  target := target
  target_physical := rfl

end SixVertexHorizontalResidualGeometricSurplusRepair
end
end StatMech.FrontierD
