/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWOuterStraddle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWOuterOrientation.Part4
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_traceStraddlesLoop_of_endpointSides
    {a b c d : ℤ} {u : Site 2}
    (C : (hypercubicLattice 2).Walk u u)
    (gamma : RlcCrossingPath a b c d)
    (h : rlc_OppositeLoopSides C
      (gamma.1 : Site 2) (gamma.2.1 : Site 2)) :
    rlc_TraceStraddlesLoop C gamma := by
  refine ⟨gamma.1, ?_, gamma.2.1, ?_, h⟩
  · exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma (gamma.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma).start_mem_support
  · exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma (gamma.2.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma).end_mem_support


theorem rlc_mixedWiredReachSet_separates_traceEndpoints_of_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    (gamma.1.1 : Site 2) ∈ rlc_mixedWiredReachSet G omega ∧
      (gamma.1.2.1 : Site 2) ∈ rlc_mixedWiredReachSet G omega ∧
      (gamma'.1.1 : Site 2) ∉ rlc_mixedWiredReachSet G omega ∧
      (gamma'.1.2.1 : Site 2) ∉ rlc_mixedWiredReachSet G omega := by
  have rightStart : (gamma.1.1 : Site 2) ∈
      rlc_pathVertices gamma.1 :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (gamma.1.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma.1).start_mem_support
  have rightEnd : (gamma.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma.1 :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (gamma.1.2.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma.1).end_mem_support
  have leftStart : (gamma'.1.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (gamma'.1.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma'.1).start_mem_support
  have leftEnd : (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (gamma'.1.2.1 : Site 2)).1
      (rlc_ambientCrossingWalk gamma'.1).end_mem_support
  exact ⟨rlc_rightPathVertex_mem_mixedWiredReachSet G omega rightStart,
    rlc_rightPathVertex_mem_mixedWiredReachSet G omega rightEnd,
    rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno leftStart,
    rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno leftEnd⟩


end Universality
end StatMech
