/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairFromReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairedBoundaryNormalized
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part2


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFiniteStripReflectedPairing

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}

variable {P : D.InteriorPairing}

variable {C : HexFiniteStripBoundaryCore R h0 D P}


@[simp] theorem pair_piece
    (S : HexFiniteStripReflectedPairing (ι := ι) C) (i : ι) :
    (S.pair i).piece = {S.neg i, S.pos i} := by
  classical
  simp [pair, HexMirrorBoundaryPair.piece,
    hexMirrorBoundaryPair_of_reflection]


theorem pair_mass_nonneg
    (S : HexFiniteStripReflectedPairing (ι := ι) C) (i : ι) :
    0 ≤ (S.pair i).mass := by
  change 0 ≤ hexClosed_countObs R.inRegion R.start h0
    (D.mid (S.neg i).vtx (S.neg i).edge) hexChi
  unfold hexClosed_countObs
  exact tsum_nonneg (fun ts =>
    hexClosed_cw_nonneg R.inRegion R.start h0
      (D.mid (S.neg i).vtx (S.neg i).edge) hexChi_pos.le ts)


end HexFiniteStripReflectedPairing
end StatMech.Universality
