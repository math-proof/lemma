/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part13
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure PairedEdgeHexCutCarrier {V I : Type*}
    (source target : I → Sym2 V) (A B : Set V) where
  alpha : Int
  beta : Int
  bottomRow : Int
  topRow : Int
  bottomX : Int
  topX : Int
  alpha_lt_beta : alpha < beta
  bottomRow_le_topRow : bottomRow ≤ topRow
  bottomX_lower : alpha ≤ bottomX
  bottomX_upper : bottomX ≤ beta
  topX_lower : alpha ≤ topX
  topX_upper : topX ≤ beta
  vertical : (hypercubicLattice 2).Walk
    ![bottomX, bottomRow] ![topX, topRow]
  vertical_mem : ∀ z ∈ vertical.support,
    z ∈ rect alpha beta bottomRow topRow
  horizontalStart : Site 2
  horizontalEnd : Site 2
  horizontalStart_mem : horizontalStart ∈ rect alpha beta bottomRow topRow
  horizontalEnd_mem : horizontalEnd ∈ rect alpha beta bottomRow topRow
  horizontalStart_left : horizontalStart 0 = alpha
  horizontalEnd_right : horizontalEnd 0 = beta
  horizontal : (hypercubicLattice 2).Walk horizontalStart horizontalEnd
  horizontal_mem : ∀ z ∈ horizontal.support,
    z ∈ rect alpha beta bottomRow topRow
  intersection_pair : ∀ z, z ∈ horizontal.support → z ∈ vertical.support →
    ∃ i : I, rlc_twoChannelFullPhysicalEdgeCrossesCut A (source i) ∧
      rlc_twoChannelFullPhysicalEdgeCrossesCut B (target i)


end
end StatMech.Universality
