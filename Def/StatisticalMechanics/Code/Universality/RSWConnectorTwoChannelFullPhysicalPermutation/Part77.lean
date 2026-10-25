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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part77
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_bookExteriorEndpointDetour {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (hypercubicLattice 2).Walk
      (gamma.1.2.1 : Site 2) (gamma'.1.1 : Site 2) := by
  let r : Site 2 := gamma.1.2.1
  let l : Site 2 := gamma'.1.1
  have hr : (![r 0, r 1] : Site 2) = r := by
    ext i
    fin_cases i <;> simp
  have hl : (![l 0, l 1] : Site 2) = l := by
    ext i
    fin_cases i <;> simp
  let rightLeg : (hypercubicLattice 2).Walk r
      ![2 * n + 2, n + 2] :=
    (sw_lshape (r 0) (r 1) (2 * n + 2) (n + 2)).copy hr rfl
  let topLeg : (hypercubicLattice 2).Walk
      ![2 * n + 2, n + 2] ![-2 * n - 2, n + 2] :=
    sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2)
  let leftLeg : (hypercubicLattice 2).Walk
      ![-2 * n - 2, n + 2] l :=
    ((sw_lshape (l 0) (l 1) (-2 * n - 2) (n + 2)).reverse).copy
      rfl hl
  exact (rightLeg.append topLeg).append leftLeg


noncomputable def rlc_bookOuterTraceNetworkArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {s : Site 2}
    (hsRight : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
    (hypercubicLattice 2).Walk s (rlc_flipX s) := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hsWR : s ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2
      hsRight
  have hsWL : rlc_flipX s ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX s)).2 hsLeft
  exact ((WR.dropUntil s hsWR).append
    (rlc_bookExteriorEndpointDetour gamma gamma')).append
      (WL.takeUntil (rlc_flipX s) hsWL)


noncomputable def rlc_bookPhysicalOuterTraceNetworkArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {s : Site 2}
    (hsRight : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
    (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm s)
      (rlc_dualReflect.symm (rlc_flipX s)) :=
  (rlc_bookOuterTraceNetworkArc gamma gamma' hsRight hsLeft).map
    rlc_dualReflectSymmLatticeHom


noncomputable def rlc_rightAmbientTraceCanonicalSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
    (hypercubicLattice 2).Walk r s := by
  let W := rlc_ambientCrossingWalk gamma.1
  have hrW : r ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr
  have hsW : s ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs
  have hsSuffix : s ∈ (W.dropUntil r hrW).support :=
    (rlc_isPath_mem_dropUntil_iff_idxOf_le W
      (rlc_ambientCrossingWalk_isPath gamma.1) hrW hsW).2 hrs
  exact (W.dropUntil r hrW).takeUntil s hsSuffix


noncomputable def rlc_bookTraceNetworkBracket {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
    (hypercubicLattice 2).Walk r (rlc_flipX s) :=
  (rlc_rightAmbientTraceCanonicalSegment gamma hr hs hrs).append
    (rlc_bookOuterTraceNetworkArc gamma gamma' hs hsLeft)


noncomputable def rlc_bookPhysicalTraceNetworkBracket {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {r s : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hs : s ∈ rlc_pathVertices gamma.1)
    (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
    (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
    (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm r)
      (rlc_dualReflect.symm (rlc_flipX s)) :=
  (rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).map
    rlc_dualReflectSymmLatticeHom


end
end StatMech.Universality
