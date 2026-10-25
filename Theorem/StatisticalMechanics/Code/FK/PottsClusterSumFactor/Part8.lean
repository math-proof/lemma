/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part8
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem measurableSet_pottsClusterSumFiberEvent
    {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (x : Site d) (a : Fin q) :
    MeasurableSet (pottsClusterSumFiberEvent boundaryColor x a) := by
  unfold pottsClusterSumFiberEvent
  apply MeasurableSet.union
  · by_cases ha : a = boundaryColor
    · rw [if_pos ha]
      exact (measurableSet_clusterInfinite x).preimage measurable_fst
    · rw [if_neg ha]
      exact MeasurableSet.empty
  · apply MeasurableSet.iUnion
    intro F
    exact ((measurableSet_pottsClusterEqEvent d x F).preimage measurable_fst).inter
      ((measurableSet_pottsLabelSumEvent F a).preimage measurable_snd)


theorem pottsClusterSumFiberEvent_eq
    {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (x : Site d) (a : Fin q) :
    pottsClusterSumFiberEvent boundaryColor x a =
      {input | pottsClusterSumSpin boundaryColor input.1 input.2 x = a} := by
  classical
  ext input
  constructor
  · intro h
    change pottsClusterSumSpin boundaryColor input.1 input.2 x = a
    rcases h with hinfinite | hfinite
    · by_cases ha : a = boundaryColor
      · have hinf : (cluster d input.1 x).Infinite := by
          simpa [pottsClusterSumFiberEvent, ha] using hinfinite
        simpa [ha] using
          pottsClusterSumSpin_of_infinite boundaryColor input.1 input.2 x hinf
      · simpa [pottsClusterSumFiberEvent, ha] using hinfinite
    · rw [Set.mem_iUnion] at hfinite
      obtain ⟨F, hcluster, hlabel⟩ := hfinite
      have hclusterEq : cluster d input.1 x = (F : Set (Site d)) :=
        hcluster
      have hfin : (cluster d input.1 x).Finite := by
        rw [hclusterEq]
        exact F.finite_toSet
      have hfinset : hfin.toFinset = F := by
        ext y
        simp [hclusterEq]
      have hsum : ∑ y : F, input.2 y = a := by
        simpa [pottsLabelSumEvent] using hlabel
      rw [pottsClusterSumSpin_of_finite boundaryColor input.1 input.2 x hfin,
        hfinset]
      exact (Finset.sum_subtype F (by simp) input.2).trans hsum
  · intro hspin
    change pottsClusterSumSpin boundaryColor input.1 input.2 x = a at hspin
    by_cases hfin : (cluster d input.1 x).Finite
    · right
      rw [Set.mem_iUnion]
      refine ⟨hfin.toFinset, ?_, ?_⟩
      · change cluster d input.1 x = (hfin.toFinset : Set (Site d))
        exact hfin.coe_toFinset.symm
      · have hsum : ∑ y ∈ hfin.toFinset, input.2 y = a := by
          rw [← pottsClusterSumSpin_of_finite
            boundaryColor input.1 input.2 x hfin]
          exact hspin
        change input.2 ∈ pottsLabelSumEvent hfin.toFinset a
        simp only [pottsLabelSumEvent, mem_cylinder, Set.mem_setOf_eq]
        have hsub : (∑ y ∈ hfin.toFinset, input.2 y) =
            ∑ y : hfin.toFinset, input.2 y :=
          Finset.sum_subtype hfin.toFinset (fun _ => Iff.rfl) input.2
        change (∑ y : hfin.toFinset, input.2 y) = a
        rw [← hsub]
        exact hsum
    · left
      have ha : a = boundaryColor := by
        have hpin := pottsClusterSumSpin_of_infinite
          boundaryColor input.1 input.2 x hfin
        exact hspin.symm.trans hpin
      have hinf : (cluster d input.1 x).Infinite := hfin
      simpa [pottsClusterSumFiberEvent, ha] using hinf


theorem measurable_pottsClusterSumSpin_apply
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (x : Site d) :
    Measurable (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor input.1 input.2 x) := by
  rw [measurable_iff_comap_le]
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have heq : (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor input.1 input.2 x) ⁻¹' t =
      ⋃ a ∈ t, pottsClusterSumFiberEvent boundaryColor x a := by
    ext input
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨pottsClusterSumSpin boundaryColor input.1 input.2 x, ⟨h, ?_⟩⟩
      rw [pottsClusterSumFiberEvent_eq]
      rfl
    · intro h
      obtain ⟨a, ha, hfiber⟩ := h
      rw [pottsClusterSumFiberEvent_eq] at hfiber
      rwa [hfiber]
  rw [heq]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ =>
    measurableSet_pottsClusterSumFiberEvent boundaryColor x a


theorem measurable_pottsClusterSumSpin
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) :
    Measurable (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor input.1 input.2) :=
  measurable_pi_lambda _ fun x =>
    measurable_pottsClusterSumSpin_apply boundaryColor x


theorem measurable_pottsClusterSumJointFactor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) :
    Measurable (pottsClusterSumJointFactor boundaryColor :
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) ->
        ((Site d -> Fin q) × ConfigSpace (Sym2 (Site d)))) :=
  (measurable_pottsClusterSumSpin boundaryColor).prodMk measurable_fst


end StatMech.FK
