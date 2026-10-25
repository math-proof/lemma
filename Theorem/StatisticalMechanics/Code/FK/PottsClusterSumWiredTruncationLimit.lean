/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTruncationLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

noncomputable section

set_option maxHeartbeats 5000000 in


theorem continuous_pottsClusterSumSpin_wiredTruncationEdge
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat) :
    Continuous (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor
          (wiredTruncationEdge d n input.1) input.2) := by
  rw [continuous_iff_continuousAt]
  intro input
  rw [continuousAt_pi]
  intro x
  let f : (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) ->
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) := fun z =>
    (wiredTruncationEdge d n z.1, z.2)
  let g : (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) -> Fin q :=
    fun z => pottsClusterSumSpin boundaryColor z.1 z.2 x
  change ContinuousAt (g ∘ f) input
  have hf : ContinuousAt f input := by
    dsimp only [f]
    exact ((continuous_wiredTruncationEdge d n).continuousAt.comp'
      continuousAt_fst).prodMk continuousAt_snd
  rcases (cluster d (f input).1 x).finite_or_infinite with
      hfinite | hinfinite
  · exact ContinuousAt.comp (f := f)
      (continuousAt_pottsClusterSumSpin_apply_of_finite
        boundaryColor (f input) x hfinite) hf
  · have hbox : ContinuousAt (fun z :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
          boxRestrict d n z.1) input :=
      (continuous_boxRestrict d n).continuousAt.comp' continuousAt_fst
    have hsingleton : ({boxRestrict d n input.1} :
        Set (ConfigSpace (Sym2 (boxVerts d n)))) ∈
          nhds (boxRestrict d n input.1) :=
      (isOpen_discrete _).mem_nhds rfl
    have hboxMem := hbox hsingleton
    have hboxEq : ∀ᶠ z in nhds input,
        boxRestrict d n z.1 = boxRestrict d n input.1 := by
      filter_upwards [hboxMem] with z hz
      simpa only [Set.mem_singleton_iff] using hz
    apply (continuousAt_const : ContinuousAt
      (fun _ : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        boundaryColor) input).congr_of_eventuallyEq
    filter_upwards [hboxEq] with z hz
    have hedge : (f z).1 = (f input).1 := by
      dsimp only [f]
      simp only [wiredTruncationEdge, hz]
    have hzInfinite : (cluster d (f z).1 x).Infinite := by
      simpa only [hedge] using hinfinite
    change g (f z) = boundaryColor
    exact pottsClusterSumSpin_of_infinite
      boundaryColor (f z).1 (f z).2 x hzInfinite


theorem tendsto_pottsClusterSumSpin_wiredTruncationEdge
    {d q : Nat} [NeZero q] (hd : 2 <= d) (boundaryColor : Fin q)
    (omega : ConfigSpace (Sym2 (Site d))) (label : Site d -> Fin q) :
    Tendsto
      (fun n => pottsClusterSumSpin boundaryColor
        (wiredTruncationEdge d n omega) label)
      atTop (nhds (pottsClusterSumSpin boundaryColor omega label)) := by
  apply tendsto_pi_nhds.2
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_pottsClusterSumSpin_wiredTruncationEdge_eq
    hd boundaryColor omega label x] with n hn
  exact hn.symm

set_option maxHeartbeats 5000000 in

theorem measurable_pottsClusterSumSpin_wiredTruncationEdge
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat) :
    Measurable (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor
          (wiredTruncationEdge d n input.1) input.2) := by
  let T : (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) ->
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) := fun input =>
    (wiredTruncationEdge d n input.1, input.2)
  have hT : Measurable T :=
    ((continuous_wiredTruncationEdge d n).measurable.comp
      measurable_fst).prodMk measurable_snd
  exact (measurable_pottsClusterSumSpin boundaryColor).comp hT


end
end StatMech.FK
