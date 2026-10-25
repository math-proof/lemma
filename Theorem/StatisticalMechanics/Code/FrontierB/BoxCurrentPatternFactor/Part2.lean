/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentPatternFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityDetermination.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
import Def.StatisticalMechanics.Code.FrontierB.BoxCurrentPatternFactor.Part2
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.IsingFK

theorem currentLocalParity_pushforward_iff
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n)
    (a : ↑(boxPullbackEdgeSubtypes d n F) → ℕ)
    (odd : ↑F → Bool) :
    currentLocalParity (pushforwardBoxLocalCurrent d n F hF a) = odd ↔
      currentLocalParity a = pullbackParityPattern d n F hF odd := by
  constructor
  · intro h
    funext e
    have hc := congrFun h (boxPullbackEdgeEquiv d n F hF e)
    simpa [currentLocalParity, pushforwardBoxLocalCurrent,
      pullbackParityPattern] using hc
  · intro h
    funext e
    have hc := congrFun h ((boxPullbackEdgeEquiv d n F hF).symm e)
    simpa [currentLocalParity, pushforwardBoxLocalCurrent,
      pullbackParityPattern] using hc

theorem preimage_currentParityPatternCylinder_extendBoxCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (odd : ↑F → Bool) :
    extendBoxCurrent d (n + 1) ⁻¹' currentParityPatternCylinder F odd =
      {m | currentLocalParity
        (restrictCurrent (boxPullbackEdgeSubtypes d n F) m) =
          pullbackParityPattern d n F hF odd} := by
  ext m
  change currentLocalParity
      (restrictCurrent F (extendBoxCurrent d (n + 1) m)) = odd ↔ _
  rw [restrictCurrent_extendBoxCurrent d n F hF m]
  exact currentLocalParity_pushforward_iff d n F hF _ odd


theorem plusBoxCurrentMeasure_pattern_factor
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d))) (hF : F ⊆ bondFinsetTouch d n)
    (a : ↑F → ℕ) :
    (plusBoxCurrentMeasure d (n + 1) beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder F {a}) =
      (plusBoxCurrentMeasure d (n + 1) beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder F (currentLocalParity a)) *
        finiteParityPMF F beta hbeta (currentLocalParity a) a := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let interior := boxCurrentInterior d (n + 1)
  let S := boxPullbackEdgeSubtypes d n F
  let p := boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one) interior
  let q := PMF.map (restrictParity G S)
    (boundaryParityPMF G beta hbeta.le interior)
  let a' := pullbackCurrentPattern d n F hF a
  have hcurrent : PMF.map (restrictCurrent S) p =
      q.bind (finiteParityPMF S beta hbeta) := by
    exact boundaryCurrentFiniteMarginal_eq_localParity_bind
      G beta hbeta interior S
  have hpoint := congrArg (fun r : PMF (↑S → ℕ) => r a') hcurrent
  change (PMF.map (restrictCurrent S) p) a' =
    q.bind (finiteParityPMF S beta hbeta) a' at hpoint
  rw [bind_finiteParityPMF_apply] at hpoint
  have hparity : currentLocalParity a' =
      pullbackParityPattern d n F hF (currentLocalParity a) := by
    rfl
  have hkernel : finiteParityPMF S beta hbeta
      (currentLocalParity a') a' =
      finiteParityPMF F beta hbeta (currentLocalParity a) a := by
    rw [finiteParityPMF_apply, finiteParityPMF_apply,
      finiteParityKernel_pullbackCurrentPattern]
  have hkernel' : finiteParityPMF S beta hbeta
      (pullbackParityPattern d n F hF (currentLocalParity a)) a' =
      finiteParityPMF F beta hbeta (currentLocalParity a) a := by
    rw [← hparity]
    exact hkernel
  have hsingle : MeasurableSet (currentCylinder F {a}) :=
    measurableSet_currentCylinder F {a}
  have hparMeas : MeasurableSet
      (currentParityPatternCylinder F (currentLocalParity a)) :=
    measurableSet_currentCylinder F _
  change Measure.map (extendBoxCurrent d (n + 1)) p.toMeasure
      (currentCylinder F {a}) =
    Measure.map (extendBoxCurrent d (n + 1)) p.toMeasure
      (currentParityPatternCylinder F (currentLocalParity a)) * _
  rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hsingle,
    preimage_currentCylinder_singleton_extendBoxCurrent d n F hF a,
    Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hparMeas,
    preimage_currentParityPatternCylinder_extendBoxCurrent d n F hF]
  rw [show p.toMeasure {m | restrictCurrent S m = a'} =
      (PMF.map (restrictCurrent S) p) a' by
    rw [← PMF.toMeasure_apply_singleton _ a' (MeasurableSet.singleton a')]
    rw [PMF.toMeasure_map_apply]
    · rfl
    · exact Measurable.of_discrete
    · exact MeasurableSet.singleton a']
  rw [hpoint, hparity, hkernel']
  congr 1
  rw [show p.toMeasure {m | currentLocalParity (restrictCurrent S m) =
        pullbackParityPattern d n F hF (currentLocalParity a)} =
      (PMF.map currentLocalParity (PMF.map (restrictCurrent S) p))
        (pullbackParityPattern d n F hF (currentLocalParity a)) by
    let odd := pullbackParityPattern d n F hF (currentLocalParity a)
    rw [← PMF.toMeasure_apply_singleton _ odd (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply currentLocalParity
      (PMF.map (restrictCurrent S) p) {odd}
      Measurable.of_discrete (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply (restrictCurrent S) p
      (currentLocalParity ⁻¹' {odd})
      Measurable.of_discrete MeasurableSet.of_discrete]
    rfl]
  rw [boundaryCurrentLocalParityPMF G beta hbeta interior S]

theorem freeBoxCurrentMeasure_pattern_factor
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d))) (hF : F ⊆ bondFinsetTouch d n)
    (a : ↑F → ℕ) :
    (freeBoxCurrentMeasure d (n + 1) beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder F {a}) =
      (freeBoxCurrentMeasure d (n + 1) beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder F (currentLocalParity a)) *
        finiteParityPMF F beta hbeta (currentLocalParity a) a := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let S := boxPullbackEdgeSubtypes d n F
  let p := sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one)
  let q := PMF.map (restrictParity G S) (freeParityPMF G beta hbeta.le)
  let a' := pullbackCurrentPattern d n F hF a
  have hcurrent : PMF.map (restrictCurrent S) p =
      q.bind (finiteParityPMF S beta hbeta) := by
    exact sourcelessCurrentFiniteMarginal_eq_localParity_bind
      G beta hbeta S
  have hpoint := congrArg (fun r : PMF (↑S → ℕ) => r a') hcurrent
  change (PMF.map (restrictCurrent S) p) a' =
    q.bind (finiteParityPMF S beta hbeta) a' at hpoint
  rw [bind_finiteParityPMF_apply] at hpoint
  have hparity : currentLocalParity a' =
      pullbackParityPattern d n F hF (currentLocalParity a) := by
    rfl
  have hkernel : finiteParityPMF S beta hbeta
      (currentLocalParity a') a' =
      finiteParityPMF F beta hbeta (currentLocalParity a) a := by
    rw [finiteParityPMF_apply, finiteParityPMF_apply,
      finiteParityKernel_pullbackCurrentPattern]
  have hkernel' : finiteParityPMF S beta hbeta
      (pullbackParityPattern d n F hF (currentLocalParity a)) a' =
      finiteParityPMF F beta hbeta (currentLocalParity a) a := by
    rw [← hparity]
    exact hkernel
  have hsingle : MeasurableSet (currentCylinder F {a}) :=
    measurableSet_currentCylinder F {a}
  have hparMeas : MeasurableSet
      (currentParityPatternCylinder F (currentLocalParity a)) :=
    measurableSet_currentCylinder F _
  change Measure.map (extendBoxCurrent d (n + 1)) p.toMeasure
      (currentCylinder F {a}) =
    Measure.map (extendBoxCurrent d (n + 1)) p.toMeasure
      (currentParityPatternCylinder F (currentLocalParity a)) * _
  rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hsingle,
    preimage_currentCylinder_singleton_extendBoxCurrent d n F hF a,
    Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hparMeas,
    preimage_currentParityPatternCylinder_extendBoxCurrent d n F hF]
  rw [show p.toMeasure {m | restrictCurrent S m = a'} =
      (PMF.map (restrictCurrent S) p) a' by
    rw [← PMF.toMeasure_apply_singleton _ a' (MeasurableSet.singleton a')]
    rw [PMF.toMeasure_map_apply]
    · rfl
    · exact Measurable.of_discrete
    · exact MeasurableSet.singleton a']
  rw [hpoint, hparity, hkernel']
  congr 1
  rw [show p.toMeasure {m | currentLocalParity (restrictCurrent S m) =
        pullbackParityPattern d n F hF (currentLocalParity a)} =
      (PMF.map currentLocalParity (PMF.map (restrictCurrent S) p))
        (pullbackParityPattern d n F hF (currentLocalParity a)) by
    let odd := pullbackParityPattern d n F hF (currentLocalParity a)
    rw [← PMF.toMeasure_apply_singleton _ odd (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply currentLocalParity
      (PMF.map (restrictCurrent S) p) {odd}
      Measurable.of_discrete (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply (restrictCurrent S) p
      (currentLocalParity ⁻¹' {odd})
      Measurable.of_discrete MeasurableSet.of_discrete]
    rfl]
  rw [sourcelessCurrentLocalParityPMF G beta hbeta S]

end StatMech.FrontierB
