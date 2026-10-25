/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourParameterCompleteness.Part5


namespace StatMech.FrontierD

theorem sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource
    (p : SixVertexFourByFourAuditedValidParameter) :
    sixVertexFourByFourAuditedValidParameterSourcePair p =
      sixVertexFourByFourAuditedCoordinateSourcePair
        (sixVertexFourByFourAuditedValidParameterCoordinate p) := by
  let c := sixVertexFourByFourAuditedValidParameterCoordinate p
  have hc := sixVertexFourByFourAuditedValidParameterCoordinate_spec p
  change sixVertexFourByFourAuditedCoordinateParameters c = p.1 at hc
  change sixVertexFourByFourAuditedParameterSourcePair p.1 =
    sixVertexFourByFourAuditedCoordinateSourcePair c
  rw [← hc]
  simp [sixVertexFourByFourAuditedParameterSourcePair,
    sixVertexFourByFourAuditedCoordinateSourcePair,
    sixVertexFourByFourAuditedCoordinateParameters,
    sixVertexFourByFourAudited_decodedSeams_coordinateRowZero]

theorem sixVertexFourByFourAuditedValidParameter_matching :
    Function.Injective sixVertexFourByFourAuditedValidParameterSourcePair /\
      Function.Injective sixVertexFourByFourAuditedValidParameterTargetPair /\
      forall p,
        SixVertexFourByFourAuditedParameterValid p.1 /\
          SixVertexFourByFourAuditedCoordinateTargetPairValid
            (sixVertexFourByFourAuditedValidParameterCoordinate p) /\
          sixVertexPairAtMostTwoCycleFineRelated
            (sixVertexFourByFourAuditedValidParameterSourcePair p)
            (sixVertexFourByFourAuditedValidParameterTargetPair p) := by
  constructor
  · intro p q hsource
    apply sixVertexFourByFourAuditedValidParameterCoordinate_injective
    apply sixVertexFourByFourAuditedCoordinateSourcePair_injective
    rw [← sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource p,
      ← sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource q]
    exact hsource
  constructor
  · intro p q htarget
    apply sixVertexFourByFourAuditedValidParameterCoordinate_injective
    apply sixVertexFourByFourAuditedCoordinateTargetPair_injective
    exact htarget
  · intro p
    constructor
    · exact p.2
    constructor
    · exact sixVertexFourByFourAuditedCoordinateTargetPair_valid _
    · rw [sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource]
      exact sixVertexFourByFourAuditedCoordinate_fineRelated _

end StatMech.FrontierD
