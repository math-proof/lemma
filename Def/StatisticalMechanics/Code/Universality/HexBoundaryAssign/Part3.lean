/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3
import Structure.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part2


namespace StatMech.Universality

open Complex

open scoped BigOperators


variable {V : Type*} [DecidableEq V]


namespace HexRegionAssign

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (A : HexRegionAssign D P R)


noncomputable def toFamilyData : HexFamilyData D P where
  cls := hexRegionClsInc R D
  dirA := (1 / 2 : ℂ) * hexUnit A.headA
  dirL := (1 / 2 : ℂ) * hexUnit A.headL
  dirTp := (1 / 2 : ℂ) * hexUnit A.headTp
  dirTm := (1 / 2 : ℂ) * hexUnit A.headTm
  dirU := (1 / 2 : ℂ) * hexUnit A.headU
  dirEqA := hexFam_straightSide_dir D A.heading A.hgeom _ A.headA A.hHeadA
  dirEqL := hexFam_straightSide_dir D A.heading A.hgeom _ A.headL A.hHeadL
  dirEqTp := hexFam_straightSide_dir D A.heading A.hgeom _ A.headTp A.hHeadTp
  dirEqTm := hexFam_straightSide_dir D A.heading A.hgeom _ A.headTm A.hHeadTm
  dirEqU := hexFam_straightSide_dir D A.heading A.hgeom _ A.headU A.hHeadU
  lam := A.lam
  taup := A.taup
  taum := A.taum
  ups := A.ups
  Fa := A.Fa
  projA := A.projA
  projL := A.projL
  projTp := A.projTp
  projTm := A.projTm
  projU := A.projU


noncomputable def toDecomp : HexBoundaryDecomp D P := A.toFamilyData.toDecomp

end HexRegionAssign
end StatMech.Universality
