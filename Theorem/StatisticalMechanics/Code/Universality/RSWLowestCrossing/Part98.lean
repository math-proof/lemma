/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part96
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_mixedAdaptiveConnectorEvent_dependsOn {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DependsOn ((rlc_mixedAdaptiveConnectorEvent gamma gamma').indicator
      (fun _ => (1 : ℝ)))
      (rlc_mixedAdaptiveEdges gamma gamma' : Set (Sym2 (Site 2))) := by
  unfold rlc_mixedAdaptiveConnectorEvent rlc_mixedAdaptiveEdges
  split
  · intro omega omega' _hagree
    simp
  · exact rlc_mixedAxisGapConnectorEvent_dependsOn _

theorem rlc_mixedAdaptiveConnectorEvent_measurableSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    MeasurableSet (rlc_mixedAdaptiveConnectorEvent gamma gamma') :=
  measurableSet_of_dependsOn
    (rlc_mixedAdaptiveConnectorEvent_dependsOn gamma gamma')

theorem rlc_rightPathEdges_disjoint_mixedAdaptiveEdges {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_pathEdges gamma.1)
      (rlc_mixedAdaptiveEdges gamma gamma') := by
  unfold rlc_mixedAdaptiveEdges
  split
  · simp
  · exact rlc_rightPathEdges_disjoint_mixedAxisGapEdges _

theorem rlc_leftPathEdges_disjoint_mixedAdaptiveEdges {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_pathEdges gamma'.1)
      (rlc_mixedAdaptiveEdges gamma gamma') := by
  unfold rlc_mixedAdaptiveEdges
  split
  · simp
  · exact rlc_leftPathEdges_disjoint_mixedAxisGapEdges _


theorem rlc_mixedAdaptiveConnector_glues_horizontal (n : ℤ) (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        rlc_mixedAdaptiveConnectorEvent gamma gamma' ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  obtain ⟨⟨hgamma, hgamma'⟩, hconnector⟩ := homega
  by_cases hdisj : Disjoint
      (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)
  · obtain ⟨G, hG⟩ :=
      rlc_axisBarrierGap?_eq_some_of_disjoint gamma gamma' hdisj
    have hmixed : omega ∈ rlc_mixedAxisGapConnectorEvent G := by
      simpa [rlc_mixedAdaptiveConnectorEvent, hG] using hconnector
    exact rlc_mixedAxisGapConnector_glues_horizontal n hn gamma gamma' G
      ⟨⟨hgamma, hgamma'⟩, hmixed⟩
  · obtain ⟨z, hz, hz'⟩ := Finset.not_disjoint_iff.mp hdisj
    apply rlc_connector_glues_horizontal n hn gamma gamma'
    exact ⟨⟨hgamma, hgamma'⟩,
      rlc_mem_connectorEvent_of_common_vertex gamma gamma' omega hz hz'⟩


end Universality
end StatMech
