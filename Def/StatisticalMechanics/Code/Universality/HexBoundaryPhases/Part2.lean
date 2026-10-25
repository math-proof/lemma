/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryPhases.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Structure.StatisticalMechanics.Code.Universality.HexBoundaryPhases


namespace StatMech.Universality

open Complex

open scoped BigOperators


variable {V : Type*} [DecidableEq V]
  {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}


namespace HexPhaseData

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (H : HexPhaseData D P R)


noncomputable def toRegionAssign : HexRegionAssign D P R where
  heading := H.heading
  hgeom := H.hgeom
  headA := H.headA
  headL := H.headL
  headTp := H.headTp
  headTm := H.headTm
  headU := H.headU
  hHeadA := H.hHeadA
  hHeadL := H.hHeadL
  hHeadTp := H.hHeadTp
  hHeadTm := H.hHeadTm
  hHeadU := H.hHeadU
  lam := H.lam
  taup := H.taup
  taum := H.taum
  ups := H.ups
  Fa := H.Fa
  projA := hexPhase_projA H.headA H.Fa H.phaseA
  projL := hexPhase_projL H.headL H.lam H.phaseL
  projTp := hexPhase_projTp H.headTp H.taup H.phaseTp
  projTm := hexPhase_projTm H.headTm H.taum H.phaseTm
  projU := hexPhase_projU H.headU H.ups H.phaseU

end HexPhaseData
end StatMech.Universality
