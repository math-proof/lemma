/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoCentralSourceGrade
    (source : sixVertexFourByTwoCentralSourceIndex) : Fin 5 :=
  ⟨(sixVertexFourByTwoSectorOneCGrade source.1).val +
      (sixVertexFourByTwoSectorOneCGrade source.2).val, by omega⟩

def sixVertexFourByTwoCentralTargetGrade
    (target : sixVertexFourByTwoCentralTargetIndex) : Fin 5 :=
  ⟨(sixVertexFourByTwoSectorTwoCGrade target.1.1).val +
      (sixVertexFourByTwoSectorTwoCGrade target.1.2).val, by omega⟩

def sixVertexFourByTwoCentralSourceZeroRank (i : Fin 28) : Fin 16 :=
  ⟨if i.val < 8 then i.val else i.val - 12, by split_ifs <;> omega⟩

def sixVertexFourByTwoCentralSourceOneRank (i : Fin 28) : Fin 12 :=
  ⟨(i.val - 8) % 12, Nat.mod_lt _ (by norm_num)⟩

def sixVertexFourByTwoCentralTargetZeroIndex (i : Fin 24) : Fin 50 :=
  ⟨if i.val < 12 then i.val else i.val + 26, by split_ifs <;> omega⟩

def sixVertexFourByTwoCentralTargetOneIndex (i : Fin 24) : Fin 50 :=
  ⟨if i.val < 8 then i.val + 12
    else if i.val < 16 then i.val + 13 else i.val + 14, by
      split_ifs <;> omega⟩


def sixVertexFourByTwoCentralNonDiagonalPair (t : Nat) : Fin 24 × Fin 24 :=
  let first : Fin 24 := ⟨(t / 23) % 24, Nat.mod_lt _ (by norm_num)⟩
  let residue := t % 23
  let secondValue := if residue < first.val then residue else residue + 1
  (first, ⟨secondValue % 24, Nat.mod_lt _ (by norm_num)⟩)

def sixVertexFourByTwoCentralRawMatching
    (source : sixVertexFourByTwoCentralSourceIndex) : Fin 50 × Fin 50 :=
  if hfirst : (sixVertexFourByTwoSectorOneCGrade source.1).val = 0 then
    if hsecond : (sixVertexFourByTwoSectorOneCGrade source.2).val = 0 then
      let flat :=
        (sixVertexFourByTwoCentralSourceZeroRank source.1).val * 16 +
          (sixVertexFourByTwoCentralSourceZeroRank source.2).val
      let target := sixVertexFourByTwoCentralNonDiagonalPair flat
      (sixVertexFourByTwoCentralTargetZeroIndex target.1,
        sixVertexFourByTwoCentralTargetZeroIndex target.2)
    else
      (sixVertexFourByTwoCentralTargetZeroIndex
          ⟨(sixVertexFourByTwoCentralSourceZeroRank source.1).val, by omega⟩,
        sixVertexFourByTwoCentralTargetOneIndex
          ⟨(sixVertexFourByTwoCentralSourceOneRank source.2).val, by omega⟩)
  else if hsecond :
      (sixVertexFourByTwoSectorOneCGrade source.2).val = 0 then
    (sixVertexFourByTwoCentralTargetOneIndex
        ⟨(sixVertexFourByTwoCentralSourceOneRank source.1).val, by omega⟩,
      sixVertexFourByTwoCentralTargetZeroIndex
        ⟨(sixVertexFourByTwoCentralSourceZeroRank source.2).val, by omega⟩)
  else
    let flat :=
      (sixVertexFourByTwoCentralSourceOneRank source.1).val * 12 +
        (sixVertexFourByTwoCentralSourceOneRank source.2).val
    let target := sixVertexFourByTwoCentralNonDiagonalPair flat
    (sixVertexFourByTwoCentralTargetOneIndex target.1,
      sixVertexFourByTwoCentralTargetOneIndex target.2)

def sixVertexFourByTwoCentralRawTargetGrade
    (target : Fin 50 × Fin 50) : Fin 5 :=
  ⟨(sixVertexFourByTwoSectorTwoCGrade target.1).val +
      (sixVertexFourByTwoSectorTwoCGrade target.2).val, by omega⟩

end
end StatMech.FrontierD
