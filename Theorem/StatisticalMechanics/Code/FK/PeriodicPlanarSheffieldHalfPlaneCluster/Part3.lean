/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.clusterWithinSetEscape_measurableSet
    (P : PeriodicGraph V) (A : Set V) (x : V) (n : Nat) :
    MeasurableSet (P.clusterWithinSetEscape A x n) :=
  MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
    P.connectedWithinSet_measurableSet A x y

omit [Countable V] in
theorem PeriodicGraph.clusterWithinSetEscape_antitone
    (P : PeriodicGraph V) (A : Set V) (x : V) :
    Antitone (P.clusterWithinSetEscape A x) := by
  intro n N hnN omega homega
  obtain ⟨y, hyOutside, hyConnect⟩ := by
    simpa only [PeriodicGraph.clusterWithinSetEscape,
      Set.mem_iUnion] using homega
  have hyOutsideSmall : y ∉ (P.orbitBox n : Set V) := by
    intro hySmall
    exact hyOutside (P.orbitBox_mono hnN hySmall)
  simp only [PeriodicGraph.clusterWithinSetEscape, Set.mem_iUnion]
  exact ⟨y, hyOutsideSmall, hyConnect⟩

omit [Countable V] in
theorem PeriodicGraph.iInter_clusterWithinSetEscape
    (P : PeriodicGraph V) (A : Set V) (x : V) :
    (⋂ n : Nat, P.clusterWithinSetEscape A x n) =
      {omega : ConfigSpace (Sym2 V) |
        (P.clusterWithinSet omega A x).Infinite} := by
  ext omega
  rw [Set.mem_iInter, Set.mem_setOf_eq,
    P.clusterWithinSet_infinite_iff_orbitBox_escape]
  constructor
  · intro h n
    obtain ⟨y, hyOutside, hyConnect⟩ := by
      simpa only [PeriodicGraph.clusterWithinSetEscape,
        Set.mem_iUnion] using h n
    exact ⟨y, hyOutside, hyConnect⟩
  · intro h n
    obtain ⟨y, hyOutside, hyConnect⟩ := h n
    simp only [PeriodicGraph.clusterWithinSetEscape, Set.mem_iUnion]
    exact ⟨y, hyOutside, hyConnect⟩


theorem PeriodicGraph.clusterWithinSetEscape_measureReal_tendsto
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (A : Set V) (x : V) :
    Tendsto (fun n => mu.real (P.clusterWithinSetEscape A x n))
      atTop (nhds (mu.real {omega : ConfigSpace (Sym2 V) |
        (P.clusterWithinSet omega A x).Infinite})) := by
  have hmeasure : Tendsto
      (fun n : Nat => mu (P.clusterWithinSetEscape A x n)) atTop
      (nhds (mu (⋂ n : Nat, P.clusterWithinSetEscape A x n))) :=
    tendsto_measure_iInter_atTop
      (fun n => (P.clusterWithinSetEscape_measurableSet A x n).nullMeasurableSet)
      (P.clusterWithinSetEscape_antitone A x)
      ⟨0, measure_ne_top mu _⟩
  rw [P.iInter_clusterWithinSetEscape A x] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure


end StatMech.FK.PeriodicPlanar
