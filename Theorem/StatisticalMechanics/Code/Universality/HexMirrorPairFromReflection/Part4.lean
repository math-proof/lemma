module
public import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
public import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
public import Def.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFiniteStripReflectedPairing

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


@[simp] theorem toMirrorPairedData_pair_angle
    (S : HexFiniteStripReflectedPairing (ι := ι) C) (i : ι) :
    ((S.toMirrorPairedData).pairs i).angle =
      hexPhase_sideTilt (S.headNeg i) + (5 / 8 : ℝ) * S.winding i := rfl


end HexFiniteStripReflectedPairing
end StatMech.Universality
