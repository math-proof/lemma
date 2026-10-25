/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Structure.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFiniteStripReflectedPairing

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


noncomputable def DCSAngles.toClassification
    (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (A : DCSAngles S) :
    HexFiniteStripMirrorPairedData.DCSClassification
      S.toMirrorPairedData where
  classOf := A.classOf
  cos_angle := by
    intro i
    rw [toMirrorPairedData_pair_angle, A.angle_eq i]
    cases A.classOf i <;> simp [hexCl, hexCt]


end HexFiniteStripReflectedPairing
end StatMech.Universality
