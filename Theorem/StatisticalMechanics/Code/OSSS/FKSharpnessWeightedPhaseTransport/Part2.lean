/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhaseTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedCoherentLimit
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport.Part2
open MeasureTheory
open Set


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPhaseTransport

open Lattice FK Percolation

open FKSharpnessWeightedPeriodic

open FKSharpnessWeightedInfiniteVolume

variable {d : Nat}


theorem phasePositivityTransport_of_coherentFiniteEnergy
    {P : Type*} (phase : Site d -> P)
    (hsurj : Function.Surjective phase)
    (mu : P -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hcoh : CovariantWeightedPhaseCoherentFiniteEnergy d phase mu) :
    WeightedPhasePositivityTransport
      (fun a _ => (((mu a : ProbabilityMeasure _) : Measure _).real
        (percolationEvent d))) := by
  intro a b beta
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (x - y)
  have hmeasure :
      (mu (phase y) : Measure (ConfigSpace (Sym2 (Site d)))) =
        (mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).map
          (ConfigSpace.shift g) := by
    simpa [g] using hcoh.1 x y
  have hbase := clusterInfiniteEvent_real_pos_iff
    (((mu (phase x) : ProbabilityMeasure _) : Measure _))
    (hcoh.2 (phase x))
    ((g⁻¹ : Multiplicative (Site d)) • origin d) (origin d)
  have hpre :
      (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) ->
        ConfigSpace (Sym2 (Site d))) ⁻¹' percolationEvent d =
      clusterInfiniteEvent d ((g⁻¹ : Multiplicative (Site d)) • origin d) := by
    have hs := shift_preimage_clusterInfiniteEvent
      (d := d) g ((g⁻¹ : Multiplicative (Site d)) • origin d)
    simpa [percolationEvent] using hs
  change 0 < (mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).real
      (percolationEvent d) <->
    0 < (mu (phase y) : Measure (ConfigSpace (Sym2 (Site d)))).real
      (percolationEvent d)
  have hmapreal :
      ((mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).map
        (ConfigSpace.shift g)).real (percolationEvent d) =
      (mu (phase x) : Measure (ConfigSpace (Sym2 (Site d)))).real
        (clusterInfiniteEvent d ((g⁻¹ : Multiplicative (Site d)) • origin d)) := by
    have hperco : MeasurableSet (percolationEvent d) := by
      simpa [percolationEvent, clusterInfiniteEvent] using
        (measurableSet_clusterInfiniteEvent (d := d) (origin d))
    rw [Measure.real, Measure.real,
      Measure.map_apply (ConfigSpace.measurable_shift g)
        hperco, hpre]
  rw [hmeasure, hmapreal]
  simpa [percolationEvent, clusterInfiniteEvent] using hbase.symm


end FKSharpnessWeightedPhaseTransport
end OSSS
end StatMech
