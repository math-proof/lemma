/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part3
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.IsingFK

theorem preimage_currentParityAvoidCylinder_extendBoxCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) :
    extendBoxCurrent d (n + 1) ⁻¹'
        currentParityAvoidCylinder F =
      {m | Disjoint
        (currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m)
        (boxPullbackEdges d n F)} := by
  ext m
  constructor
  · intro hm
    change ∀ e ∈ F, Even (extendBoxCurrent d (n + 1) m e) at hm
    change Disjoint
      (currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m)
      (boxPullbackEdges d n F)
    rw [Finset.disjoint_left]
    intro e heParity heBox
    have heEdge := boxPullbackEdges_subset d n F heBox
    let es : (StatMech.FK.boxGraph d (n + 1)).edgeFinset := ⟨e, heEdge⟩
    have hodd : Odd (m es) := by
      simpa [es] using
        (mem_currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m es).mp
          heParity
    have heF : StatMech.FK.edgeIncl d (n + 1) e ∈ F :=
      (Finset.mem_filter.mp heBox).2
    have heven := hm (StatMech.FK.edgeIncl d (n + 1) e) heF
    have heq : extendBoxCurrent d (n + 1) m
        (StatMech.FK.edgeIncl d (n + 1) e) = m es := by
      exact extendBoxCurrent_included d (n + 1) m es
    rw [heq] at heven
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  · intro hm e heFmem
    change Disjoint
      (currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m)
      (boxPullbackEdges d n F) at hm
    have himage : e ∈
        (boxPullbackEdges d n F).image (StatMech.FK.edgeIncl d (n + 1)) := by
      rw [image_boxPullbackEdges d n F hF]
      exact heFmem
    rw [Finset.mem_image] at himage
    obtain ⟨f, hfBox, hfe⟩ := himage
    have hfEdge := boxPullbackEdges_subset d n F hfBox
    let fs : (StatMech.FK.boxGraph d (n + 1)).edgeFinset := ⟨f, hfEdge⟩
    have hnotOdd : ¬ Odd (m fs) := by
      intro hodd
      have hfParity : f ∈
          currentParitySupport (StatMech.FK.boxGraph d (n + 1)) m := by
        exact (mem_currentParitySupport
          (StatMech.FK.boxGraph d (n + 1)) m fs).mpr hodd
      exact Finset.disjoint_left.mp hm hfParity hfBox
    have heq : extendBoxCurrent d (n + 1) m e = m fs := by
      rw [← hfe]
      exact extendBoxCurrent_included d (n + 1) m fs
    rw [heq]
    exact Nat.not_odd_iff_even.mp hnotOdd

theorem plusBoxCurrentMeasure_parityAvoid_eq_plusIntegral
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 (Site d))) (hF : F ⊆ bondFinsetTouch d n) :
    (plusBoxCurrentMeasure d (n + 1) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F) =
      ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card) := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let interior := boxCurrentInterior d (n + 1)
  have hbox : boxPullbackEdges d n F ⊆ G.edgeFinset :=
    boxPullbackEdges_subset d n F
  have hcard : (boxPullbackEdges d n F).card = F.card := by
    have hi := congrArg Finset.card (image_boxPullbackEdges d n F hF)
    rw [Finset.card_image_of_injective _
      (StatMech.FK.edgeIncl_injective d (n + 1))] at hi
    exact hi
  have hmeas : MeasurableSet (currentParityAvoidCylinder F) := by
    have hset : currentParityAvoidCylinder F =
        (restrictCurrent F) ⁻¹' {a : ↑F → ℕ | ∀ e, Even (a e)} := by
      ext m
      simp [currentParityAvoidCylinder, restrictCurrent]
    rw [hset]
    exact (continuous_restrictCurrent F).measurable MeasurableSet.of_discrete
  calc
    (plusBoxCurrentMeasure d (n + 1) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F) =
      (boundaryCurrentPMF G beta (fun _ => 1) hbeta
        (fun _ => zero_le_one) interior).toMeasure
          {m | Disjoint (currentParitySupport G m)
            (boxPullbackEdges d n F)} := by
        change Measure.map (extendBoxCurrent d (n + 1))
          (boundaryCurrentPMF G beta (fun _ => 1) hbeta
            (fun _ => zero_le_one) interior).toMeasure
            (currentParityAvoidCylinder F) = _
        rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hmeas,
          preimage_currentParityAvoidCylinder_extendBoxCurrent d n F hF]
    _ = (boundaryParityPMF G beta hbeta interior).toMeasure
          {H | Disjoint H (boxPullbackEdges d n F)} := by
        rw [boundaryParityPMF, PMF.toMeasure_map_apply]
        · rfl
        · exact Measurable.of_discrete
        · exact MeasurableSet.of_discrete
    _ = ENNReal.ofReal
        (((∑ s : ConfigSpace ↑interior,
            boltzmannJ G beta (fun _ => 1) (extendInteriorPlus interior s) *
              Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F)
                (extendInteriorPlus interior s))) /
          boundaryPartitionJ G beta (fun _ => 1) interior) *
            Real.cosh beta ^ (boxPullbackEdges d n F).card) :=
      boundaryParityMeasure_avoid_eq_spinExpectation G beta hbeta interior
        (boxPullbackEdges d n F) hbox
    _ = _ := by
      rw [boundarySpinExpectation_box_eq_plusIntegral d n beta F hF, hcard]

end StatMech.FrontierB
