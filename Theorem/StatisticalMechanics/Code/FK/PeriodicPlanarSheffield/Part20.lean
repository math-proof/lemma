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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part20
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.pairMergeError_measurableSet
    (P : PeriodicGraph V) (x y : V) (N : ℕ) :
    MeasurableSet (P.pairMergeError x y N) :=
  ((P.measurableSet_cluster_infinite x).inter
    (P.measurableSet_cluster_infinite y)).diff
      (P.connectedWithinOrbit_measurableSet x y N)

theorem PeriodicGraph.pairMergeError_antitone
    (P : PeriodicGraph V) (x y : V) :
    Antitone (P.pairMergeError x y) := by
  intro n m hnm omega herror
  exact ⟨herror.1, fun hm =>
    herror.2 (P.connectedWithinOrbit_mono x y hnm hm)⟩

theorem PeriodicGraph.iInter_pairMergeError_subset_not_unique
    (P : PeriodicGraph V) (x y : V) :
    (⋂ N, P.pairMergeError x y N) ⊆
      {omega | P.HasUniqueInfiniteCluster omega}ᶜ := by
  intro omega herror hunique
  have hzero := Set.mem_iInter.mp herror 0
  have hxinf := hzero.1.1
  have hyinf := hzero.1.2
  have hreach := hunique.2 x y hxinf hyinf
  have htwo : omega ∈ P.twoPointEvent x y := hreach
  rw [← P.iUnion_connectedWithinOrbit x y] at htwo
  obtain ⟨N, hN⟩ := Set.mem_iUnion.mp htwo
  exact (Set.mem_iInter.mp herror N).2 hN


theorem PeriodicGraph.pairMergeError_real_tendsto_zero
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (x y : V) :
    Tendsto (fun N => mu.real (P.pairMergeError x y N))
      atTop (nhds 0) := by
  have hlim : Tendsto (fun N : ℕ => mu (P.pairMergeError x y N)) atTop
      (nhds (mu (⋂ N, P.pairMergeError x y N))) :=
    tendsto_measure_iInter_atTop
      (μ := mu)
      (fun N => (P.pairMergeError_measurableSet x y N).nullMeasurableSet)
      (P.pairMergeError_antitone x y)
      ⟨0, measure_ne_top mu _⟩
  have hcomplement :
      mu {omega | P.HasUniqueInfiniteCluster omega}ᶜ = 0 :=
    (prob_compl_eq_zero_iff P.measurableSet_hasUniqueInfiniteCluster).2 hunique
  have hinter : mu (⋂ N, P.pairMergeError x y N) = 0 :=
    measure_mono_null (P.iInter_pairMergeError_subset_not_unique x y)
      hcomplement
  rw [hinter] at hlim
  exact (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hlim


end StatMech.FK.PeriodicPlanar
