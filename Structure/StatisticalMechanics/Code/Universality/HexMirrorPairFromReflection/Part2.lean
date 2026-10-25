/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part4


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFiniteStripReflectedPairing

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


structure DCSAngles (S : HexFiniteStripReflectedPairing (ι := ι) C) where
  classOf : ι → HexPairedBoundaryClass
  angle_eq : ∀ i,
    hexPhase_sideTilt (S.headNeg i) + (5 / 8 : ℝ) * S.winding i =
      match classOf i with
      | .side => 3 * Real.pi / 8
      | .slant => Real.pi / 4
      | .top => 0


end HexFiniteStripReflectedPairing
end StatMech.Universality
