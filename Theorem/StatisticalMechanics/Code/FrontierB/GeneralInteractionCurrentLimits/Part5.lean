/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part7
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


set_option maxHeartbeats 800000 in


theorem generalFreeBoxCurrentMeasure_edge_tail {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : (interactionBoxGraph d n).edgeFinset) (K : Nat) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m (interactionBoxEdgeIncl d n e)} =
      (sourcelessCurrentMeasure (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e)) :
          Measure (EdgeCurrent (interactionBoxGraph d n)))
        {m | K <= m e} := by
  change Measure.map (extendInteractionBoxCurrent d n)
      ((sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure)
        {m | K <= m (interactionBoxEdgeIncl d n e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K <= m (interactionBoxEdgeIncl d n e)} :=
    (measurable_pi_apply (interactionBoxEdgeIncl d n e)) MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hset]
  congr 1
  ext m
  simp

set_option maxHeartbeats 800000 in


theorem generalPlusBoxCurrentMeasure_edge_tail {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : (interactionBoxGraph d (2 * n + 1)).edgeFinset) (K : Nat) :
    (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m (interactionBoxEdgeIncl d (2 * n + 1) e)} =
      (boundaryCurrentMeasure (interactionBoxGraph d (2 * n + 1)) beta
        (interactionBoxCoupling J (2 * n + 1)) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))
        (interactionPlusInterior d n) :
          Measure (EdgeCurrent (interactionBoxGraph d (2 * n + 1))))
        {m | K <= m e} := by
  change Measure.map (extendInteractionBoxCurrent d (2 * n + 1))
      ((boundaryCurrentPMF (interactionBoxGraph d (2 * n + 1)) beta
        (interactionBoxCoupling J (2 * n + 1)) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))
        (interactionPlusInterior d n)).toMeasure)
        {m | K <= m (interactionBoxEdgeIncl d (2 * n + 1) e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K <= m (interactionBoxEdgeIncl d (2 * n + 1) e)} :=
    (measurable_pi_apply
      (interactionBoxEdgeIncl d (2 * n + 1) e)) MeasurableSet.of_discrete
  rw [Measure.map_apply
    (measurable_extendInteractionBoxCurrent d (2 * n + 1)) hset]
  congr 1
  ext m
  simp

set_option maxHeartbeats 800000 in


theorem generalFreeBoxCurrentMeasure_edge_inverse_tail_le {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : Sym2 (Site d)) (K : Nat) (hK : 0 < K) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m e} <=
      ENNReal.ofReal (Real.exp (beta * J e)) / K := by
  by_cases he : e ∈ Set.range (interactionBoxEdgeIncl d n)
  · obtain ⟨f, rfl⟩ := he
    rw [generalFreeBoxCurrentMeasure_edge_tail]
    calc
      (sourcelessCurrentMeasure (interactionBoxGraph d n) beta
          (interactionBoxCoupling J n) hbeta
            (fun e => hJ (Sym2.map Subtype.val e)) :
          Measure (EdgeCurrent (interactionBoxGraph d n)))
          {m | K <= m f} <=
          ENNReal.ofReal
            (Real.exp (beta * interactionBoxCoupling J n f.1) / K) :=
        sourcelessCurrentMeasure_edge_inverse_tail_le
          (interactionBoxGraph d n) beta (interactionBoxCoupling J n)
          hbeta (fun e => hJ (Sym2.map Subtype.val e)) f K hK
      _ = ENNReal.ofReal
          (Real.exp (beta * J (interactionBoxEdgeIncl d n f))) / K := by
        rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 hK)]
        simp [interactionBoxCoupling, interactionBoxEdgeIncl]
  · change Measure.map (extendInteractionBoxCurrent d n)
      ((sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure)
        {m | K <= m e} <= _
    have hset : MeasurableSet
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K <= m e} :=
      (measurable_pi_apply e) MeasurableSet.of_discrete
    rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hset]
    have hempty : extendInteractionBoxCurrent d n ⁻¹'
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K <= m e} = ∅ := by
      ext m
      simp [extendInteractionBoxCurrent_outside d n m e he,
        Nat.not_le_of_lt hK]
    rw [hempty, measure_empty]
    exact bot_le

set_option maxHeartbeats 800000 in


theorem generalPlusBoxCurrentMeasure_edge_inverse_tail_le {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : Sym2 (Site d)) (K : Nat) (hK : 0 < K) :
    (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m e} <=
      ENNReal.ofReal (Real.exp (beta * J e)) / K := by
  let r := 2 * n + 1
  by_cases he : e ∈ Set.range (interactionBoxEdgeIncl d r)
  · obtain ⟨f, rfl⟩ := he
    change (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m (interactionBoxEdgeIncl d (2 * n + 1) f)} <= _
    rw [generalPlusBoxCurrentMeasure_edge_tail]
    calc
      (boundaryCurrentMeasure (interactionBoxGraph d (2 * n + 1)) beta
          (interactionBoxCoupling J (2 * n + 1)) hbeta
            (fun e => hJ (Sym2.map Subtype.val e))
          (interactionPlusInterior d n) :
          Measure (EdgeCurrent (interactionBoxGraph d (2 * n + 1))))
          {m | K <= m f} <=
          ENNReal.ofReal
            (Real.exp (beta * interactionBoxCoupling J (2 * n + 1) f.1) / K) :=
        boundaryCurrentMeasure_edge_inverse_tail_le
          (interactionBoxGraph d (2 * n + 1)) beta
          (interactionBoxCoupling J (2 * n + 1)) hbeta
            (fun e => hJ (Sym2.map Subtype.val e))
          (interactionPlusInterior d n) f K hK
      _ = ENNReal.ofReal
          (Real.exp (beta * J (interactionBoxEdgeIncl d (2 * n + 1) f))) / K := by
        rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 hK)]
        simp [interactionBoxCoupling, interactionBoxEdgeIncl]
  · change Measure.map (extendInteractionBoxCurrent d (2 * n + 1))
      ((boundaryCurrentPMF (interactionBoxGraph d (2 * n + 1)) beta
        (interactionBoxCoupling J (2 * n + 1)) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))
        (interactionPlusInterior d n)).toMeasure) {m | K <= m e} <= _
    have hset : MeasurableSet
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K <= m e} :=
      (measurable_pi_apply e) MeasurableSet.of_discrete
    rw [Measure.map_apply
      (measurable_extendInteractionBoxCurrent d (2 * n + 1)) hset]
    have hempty : extendInteractionBoxCurrent d (2 * n + 1) ⁻¹'
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K <= m e} = ∅ := by
      ext m
      have he' : e ∉ Set.range
          (interactionBoxEdgeIncl d (2 * n + 1)) := by
        simpa only [r] using he
      simp [extendInteractionBoxCurrent_outside d (2 * n + 1) m e he',
        Nat.not_le_of_lt hK]
    rw [hempty, measure_empty]
    exact bot_le


theorem generalFreeBoxCurrentMeasure_uniform_inverse_tail_le {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : Sym2 (Site d)) (K : Nat) (hK : 0 < K) :
    (generalFreeBoxCurrentMeasure I.coupling I.nonneg n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m e} <=
      ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
  calc
    _ <= ENNReal.ofReal (Real.exp (beta * I.coupling e)) / K :=
      generalFreeBoxCurrentMeasure_edge_inverse_tail_le
        I.coupling I.nonneg n beta hbeta e K hK
    _ <= ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
      gcongr
      exact I.coupling_le_strength e


theorem generalPlusBoxCurrentMeasure_uniform_inverse_tail_le {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : Sym2 (Site d)) (K : Nat) (hK : 0 < K) :
    (generalPlusBoxCurrentMeasure I.coupling I.nonneg n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m e} <=
      ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
  calc
    _ <= ENNReal.ofReal (Real.exp (beta * I.coupling e)) / K :=
      generalPlusBoxCurrentMeasure_edge_inverse_tail_le
        I.coupling I.nonneg n beta hbeta e K hK
    _ <= ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
      gcongr
      exact I.coupling_le_strength e


theorem generalFreeBoxCurrentMeasure_tight {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (beta : Real) (hbeta : 0 <= beta) :
    IsTightMeasureSet (Set.range fun n =>
      (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
  apply isTightMeasureSet_range_of_coordinate_tight
  intro e epsilon hepsilon
  obtain ⟨K, hKpos, hK⟩ := ENNReal.exists_nat_pos_mul_gt
    hepsilon.ne' (ENNReal.ofReal_ne_top :
      ENNReal.ofReal (Real.exp (beta * J e)) ≠ ∞)
  refine ⟨K, fun n => ?_⟩
  exact (generalFreeBoxCurrentMeasure_edge_inverse_tail_le
    J hJ n beta hbeta e K hKpos).trans
      (ENNReal.div_le_of_le_mul' hK.le)


theorem generalPlusBoxCurrentMeasure_tight {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (beta : Real) (hbeta : 0 <= beta) :
    IsTightMeasureSet (Set.range fun n =>
      (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
  apply isTightMeasureSet_range_of_coordinate_tight
  intro e epsilon hepsilon
  obtain ⟨K, hKpos, hK⟩ := ENNReal.exists_nat_pos_mul_gt
    hepsilon.ne' (ENNReal.ofReal_ne_top :
      ENNReal.ofReal (Real.exp (beta * J e)) ≠ ∞)
  refine ⟨K, fun n => ?_⟩
  exact (generalPlusBoxCurrentMeasure_edge_inverse_tail_le
    J hJ n beta hbeta e K hKpos).trans
      (ENNReal.div_le_of_le_mul' hK.le)


theorem generalFreePlusBoxCurrentMeasure_joint_subsequence {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (beta : Real) (hbeta : 0 <= beta) :
    ∃ (nuFree nuPlus : ProbabilityMeasure
        (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : Nat -> Nat), StrictMono phi ∧
        WeakCurrentConverges
          ((fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta) ∘ phi)
          nuFree ∧
        WeakCurrentConverges
          ((fun n => generalPlusBoxCurrentMeasure J hJ n beta hbeta) ∘ phi)
          nuPlus := by
  obtain ⟨nuFree, phiFree, hphiFree, hfree⟩ :=
    weakCurrent_subsequence_of_tight
      (fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta)
      (generalFreeBoxCurrentMeasure_tight J hJ beta hbeta)
  have hplusTight : IsTightMeasureSet
      (Set.range fun n =>
        (generalPlusBoxCurrentMeasure J hJ (phiFree n) beta hbeta :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))) :=
    (generalPlusBoxCurrentMeasure_tight J hJ beta hbeta).subset
      (Set.range_comp_subset_range phiFree
        (fun n => (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))))
  obtain ⟨nuPlus, phiPlus, hphiPlus, hplus⟩ :=
    weakCurrent_subsequence_of_tight
      ((fun n => generalPlusBoxCurrentMeasure J hJ n beta hbeta) ∘ phiFree)
      hplusTight
  refine ⟨nuFree, nuPlus, phiFree ∘ phiPlus,
    hphiFree.comp hphiPlus, ?_, hplus⟩
  exact hfree.comp hphiPlus.tendsto_atTop


end StatMech.FrontierB
