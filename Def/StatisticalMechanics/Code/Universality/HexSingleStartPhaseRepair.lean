/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexProjPhaseClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexSingleStartPhaseRepair


namespace StatMech.Universality

open Complex

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexSingleStartPhaseData

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (H : HexSingleStartPhaseData D P R)

noncomputable def toHalfStartRegionAssign : HexRegionAssign D P R where
  heading := H.heading
  hgeom := H.hgeom
  headA := 4
  headL := H.headL
  headTp := H.headTp
  headTm := H.headTm
  headU := H.headU
  hHeadA := H.heading_eq_four_on_startFiber
  hHeadL := H.hHeadL
  hHeadTp := H.hHeadTp
  hHeadTm := H.hHeadTm
  hHeadU := H.hHeadU
  lam := H.lam
  taup := H.taup
  taum := H.taum
  ups := H.ups
  Fa := H.Fa / 2
  projA := H.startProjection
  projL := hexPhase_projL H.headL H.lam H.phaseL
  projTp := hexPhase_projTp H.headTp H.taup H.phaseTp
  projTm := hexPhase_projTm H.headTm H.taum H.phaseTm
  projU := hexPhase_projU H.headU H.ups H.phaseU

end HexSingleStartPhaseData
end StatMech.Universality
