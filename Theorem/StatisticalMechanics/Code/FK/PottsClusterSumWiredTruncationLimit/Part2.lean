/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncationLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncationLimit
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

noncomputable section

theorem tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure_of_tendsto
    {d q : Nat} [NeZero q] {I : Type*} {L : Filter I}
    (boundaryColor : Fin q)
    (edgeSeq : I -> ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (edgeLimit : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (n : Nat) (hedge : Tendsto edgeSeq L (nhds edgeLimit)) :
    Tendsto (fun i => wiredTruncatedPottsClusterSumSpinProbabilityMeasure
      boundaryColor (edgeSeq i) n) L
      (nhds (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
        boundaryColor edgeLimit n)) := by
  let labelMeasure := pottsIIDLabelProbabilityMeasure d q
  have hpairs : Tendsto (fun i => (edgeSeq i, labelMeasure)) L
      (nhds (edgeLimit, labelMeasure)) := by
    rw [nhds_prod_eq]
    exact hedge.prodMk tendsto_const_nhds
  have hsource : Tendsto (fun i =>
      pottsClusterFactorInputProbabilityMeasure (q := q) (edgeSeq i)) L
      (nhds (pottsClusterFactorInputProbabilityMeasure
        (q := q) edgeLimit)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpairs
  simpa only [wiredTruncatedPottsClusterSumSpinProbabilityMeasure] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun i => pottsClusterFactorInputProbabilityMeasure (q := q) (edgeSeq i))
      (pottsClusterFactorInputProbabilityMeasure (q := q) edgeLimit)
      hsource
      (continuous_pottsClusterSumSpin_wiredTruncationEdge boundaryColor n)


theorem tendsto_wiredTruncatedPottsClusterSumSpinProbabilityMeasure
    {d q : Nat} [NeZero q] (hd : 2 <= d) (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    Tendsto (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
      boundaryColor edgeMeasure) atTop
      (nhds ((pottsClusterSumJointProbabilityMeasure
        boundaryColor edgeMeasure).map
          continuous_fst.measurable.aemeasurable)) := by
  let source : ProbabilityMeasure
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
    pottsClusterFactorInputProbabilityMeasure edgeMeasure
  let f : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ->
      PottsConfig d q := fun input =>
    pottsClusterSumSpin boundaryColor input.1 input.2
  let fn : Nat -> ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) ->
      PottsConfig d q := fun n input =>
    pottsClusterSumSpin boundaryColor
      (wiredTruncationEdge d n input.1) input.2
  have hf : Measurable f := measurable_pottsClusterSumSpin boundaryColor
  have hfn : forall n, Measurable (fn n) := fun n =>
    measurable_pottsClusterSumSpin_wiredTruncationEdge boundaryColor n
  let limitSpin : ProbabilityMeasure (PottsConfig d q) :=
    source.map hf.aemeasurable
  have hlimit : Tendsto
      (wiredTruncatedPottsClusterSumSpinProbabilityMeasure
        boundaryColor edgeMeasure) atTop (nhds limitSpin) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro g
    have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := (source : Measure _))
      (F := fun n input => g (fn n input))
      (f := fun input => g (f input))
      (fun _ => norm g)
      (fun n => (g.continuous.measurable.comp (hfn n)).aestronglyMeasurable)
      (integrable_const (norm g))
      (by
        intro n
        filter_upwards with input
        exact g.norm_coe_le_norm (fn n input))
      (by
        filter_upwards with input
        exact g.continuous.continuousAt.tendsto.comp
          (tendsto_pottsClusterSumSpin_wiredTruncationEdge
            hd boundaryColor input.1 input.2))
    have hmapn (n : Nat) :
        (∫ z, g z
            ∂(wiredTruncatedPottsClusterSumSpinProbabilityMeasure
              boundaryColor edgeMeasure n : Measure _)) =
          ∫ input, g (fn n input) ∂(source : Measure _) := by
      unfold wiredTruncatedPottsClusterSumSpinProbabilityMeasure
      change (∫ z, g z ∂Measure.map (fn n) (source : Measure _)) = _
      rw [MeasureTheory.integral_map (hfn n).aemeasurable
        g.continuous.aestronglyMeasurable]
    have hmaplim :
        (∫ z, g z ∂(limitSpin : Measure _)) =
          ∫ input, g (f input) ∂(source : Measure _) := by
      dsimp only [limitSpin]
      change (∫ z, g z ∂Measure.map f (source : Measure _)) = _
      rw [MeasureTheory.integral_map hf.aemeasurable
        g.continuous.aestronglyMeasurable]
    simpa only [hmapn, hmaplim] using hdct
  have htarget : limitSpin =
      (pottsClusterSumJointProbabilityMeasure boundaryColor edgeMeasure).map
        continuous_fst.measurable.aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    calc
      Measure.map f (source : Measure _) =
          Measure.map (Prod.fst ∘ pottsClusterSumJointFactor boundaryColor)
            (source : Measure _) := rfl
      _ = Measure.map Prod.fst
          (Measure.map (pottsClusterSumJointFactor boundaryColor)
            (source : Measure _)) :=
        (Measure.map_map measurable_fst
          (measurable_pottsClusterSumJointFactor boundaryColor)).symm
  rwa [← htarget]

end
end StatMech.FK
