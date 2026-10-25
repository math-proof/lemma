/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part18
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.connectedWithinOrbit_measurableSet
    (P : PeriodicGraph V) (x y : V) (N : ℕ) :
    MeasurableSet (P.connectedWithinOrbit x y N) := by
  have heq : P.connectedWithinOrbit x y N =
      ⋃ l : List V, if
        (x :: l).getLast (List.cons_ne_nil _ _) = y ∧
          ∀ v ∈ x :: l, v ∈ P.orbitBox (P.bufferedRadius N)
        then {omega | List.IsChain (P.openSubgraph omega).Adj (x :: l)}
        else ∅ := by
    ext omega
    simp only [PeriodicGraph.connectedWithinOrbit, Set.mem_setOf_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨l, hchain, hlast, hbox⟩
      refine ⟨l, ?_⟩
      rw [if_pos ⟨hlast, hbox⟩]
      exact hchain
    · rintro ⟨l, hl⟩
      split_ifs at hl with h
      · exact ⟨l, hl, h.1, h.2⟩
      · exact False.elim (by simpa using hl)
  rw [heq]
  exact MeasurableSet.iUnion fun l => by
    split_ifs
    · exact P.measurableSet_openChain_sheffield (x :: l)
    · exact MeasurableSet.empty

theorem PeriodicGraph.connectedWithinOrbit_isIncreasing
    (P : PeriodicGraph V) (x y : V) (N : ℕ) :
    IsIncreasing (P.connectedWithinOrbit x y N) := by
  intro omega eta home
  rintro ⟨l, hchain, hlast, hbox⟩
  refine ⟨l, hchain.imp ?_, hlast, hbox⟩
  intro a b hab
  rw [P.openSubgraph_adj] at hab ⊢
  refine ⟨hab.1, Bool.eq_true_of_true_le ?_⟩
  simpa [hab.2] using home s(a, b)

theorem PeriodicGraph.connectedWithinOrbit_mono
    (P : PeriodicGraph V) (x y : V) :
    Monotone (P.connectedWithinOrbit x y) := by
  intro n m hnm omega
  rintro ⟨l, hchain, hlast, hbox⟩
  refine ⟨l, hchain, hlast, ?_⟩
  intro v hv
  exact P.orbitBox_mono (P.bufferedRadius_strictMono.monotone hnm) (hbox v hv)

theorem PeriodicGraph.iUnion_connectedWithinOrbit
    (P : PeriodicGraph V) (x y : V) :
    (⋃ N, P.connectedWithinOrbit x y N) = P.twoPointEvent x y := by
  ext omega
  simp only [Set.mem_iUnion, PeriodicGraph.connectedWithinOrbit,
    Set.mem_setOf_eq, PeriodicGraph.twoPointEvent]
  constructor
  · rintro ⟨N, l, hchain, hlast, _hbox⟩
    exact (P.reachable_iff_openChain_sheffield omega x y).2
      ⟨l, hchain, hlast⟩
  · intro hreach
    obtain ⟨l, hchain, hlast⟩ :=
      (P.reachable_iff_openChain_sheffield omega x y).1 hreach
    obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (x :: l).toFinset
    refine ⟨N, l, hchain, hlast, ?_⟩
    intro v hv
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN v (by simpa using hv))


end StatMech.FK.PeriodicPlanar
