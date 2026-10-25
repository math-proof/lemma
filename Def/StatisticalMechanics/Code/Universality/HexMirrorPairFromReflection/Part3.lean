/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part3


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFiniteStripReflectedPairing

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


noncomputable def toMirrorPairedData
    (S : HexFiniteStripReflectedPairing (ι := ι) C) :
    HexFiniteStripMirrorPairedData (ι := ι) C where
  heading := S.heading
  hgeom := S.hgeom
  startIncidence := S.startIncidence
  start_mid := S.start_mid
  start_heading := S.start_heading
  pairs := S.pair
  boundary_partition := by
    simpa only [pair_piece] using S.boundary_partition
  start_pairs_disjoint := by
    simpa only [pair_piece] using S.start_pairs_disjoint
  pairs_disjoint := by
    simpa only [pair_piece] using S.pairs_disjoint

end HexFiniteStripReflectedPairing
end StatMech.Universality
