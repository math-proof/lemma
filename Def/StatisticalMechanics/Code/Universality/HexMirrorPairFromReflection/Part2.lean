/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Structure.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFiniteStripReflectedPairing

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


noncomputable def pair (S : HexFiniteStripReflectedPairing (ι := ι) C)
    (i : ι) : HexMirrorBoundaryPair D S.heading :=
  hexMirrorBoundaryPair_of_reflection C S.heading (S.neg i) (S.pos i)
    (S.pair_ne i) (S.headNeg i) (S.headPos i)
    (S.hHeadNeg i) (S.hHeadPos i) (S.midpoint_reflect i)
    S.region_reflect (S.winding i) (S.winding_neg i) (S.tilt_reflect i)

end HexFiniteStripReflectedPairing
end StatMech.Universality
