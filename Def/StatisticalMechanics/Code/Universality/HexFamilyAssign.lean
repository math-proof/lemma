/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Structure.StatisticalMechanics.Code.Universality.HexFamilyAssign


namespace StatMech.Universality

open Complex

open scoped BigOperators


namespace HexFamilyData

variable {V : Type*} [DecidableEq V] {D : HexDomain V} {P : D.InteriorPairing}
  (F : HexFamilyData D P)


noncomputable def toDecomp : HexBoundaryDecomp D P where
  A := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 0), F.dirA, F.dirEqA⟩
  L := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 1), F.dirL, F.dirEqL⟩
  Tp := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 2), F.dirTp, F.dirEqTp⟩
  Tm := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 3), F.dirTm, F.dirEqTm⟩
  U := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 4), F.dirU, F.dirEqU⟩
  lam := F.lam
  taup := F.taup
  taum := F.taum
  ups := F.ups
  Fa := F.Fa
  partition := hexFam_part5 (D.incidences \ P.interior) F.cls
  disjAL := hexFam_disj5 _ F.cls 0 1 (by decide)
  disjATp := hexFam_disj5 _ F.cls 0 2 (by decide)
  disjATm := hexFam_disj5 _ F.cls 0 3 (by decide)
  disjAU := hexFam_disj5 _ F.cls 0 4 (by decide)
  disjLTp := hexFam_disj5 _ F.cls 1 2 (by decide)
  disjLTm := hexFam_disj5 _ F.cls 1 3 (by decide)
  disjLU := hexFam_disj5 _ F.cls 1 4 (by decide)
  disjTpTm := hexFam_disj5 _ F.cls 2 3 (by decide)
  disjTpU := hexFam_disj5 _ F.cls 2 4 (by decide)
  disjTmU := hexFam_disj5 _ F.cls 3 4 (by decide)
  projA := F.projA
  projL := F.projL
  projTp := F.projTp
  projTm := F.projTm
  projU := F.projU

end HexFamilyData
end StatMech.Universality
