/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part31
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_target_or_sourceTraceResidue
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj f g)
    (hfailure :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure
        gamma gamma' B f g) :
    ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_reflectedPathEdges gamma'.1) ∨
      ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
        target.1.map Subtype.val =
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
          rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalSourceResidue
            gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) f g := by
  rcases hfailure with htarget | ⟨target, htarget, hcross, hsourceBad⟩
  · exact Or.inl htarget
  · refine Or.inr ⟨target, htarget, hcross, hsourceBad, ?_⟩
    exact
      (rlc_twoChannelFullPhysical_sourceBad_exclusiveReflectedLeft_traceResidue_or_otherLocation
        gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
          (rlc_twoChannelFullPhysicalCutInteriorConfig_failure
            gamma gamma' A hAright hAleft)
          hfg hsourceBad)


end
end StatMech.Universality
