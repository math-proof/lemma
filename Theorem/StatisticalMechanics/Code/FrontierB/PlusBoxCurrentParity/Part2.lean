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
import Def.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part2
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.IsingFK

theorem boxPullbackEdges_subset (d n : ℕ)
    (F : Finset (Sym2 (Site d))) :
    boxPullbackEdges d n F ⊆
      (StatMech.FK.boxGraph d (n + 1)).edgeFinset :=
  Finset.filter_subset _ _

theorem image_boxPullbackEdges
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) :
    (boxPullbackEdges d n F).image (StatMech.FK.edgeIncl d (n + 1)) = F := by
  ext e
  constructor
  · intro he
    rw [Finset.mem_image] at he
    obtain ⟨f, hf, rfl⟩ := he
    exact (Finset.mem_filter.mp hf).2
  · intro he
    have himage := StatMech.IsingFK.hbx_touch_subset_image d n (hF he)
    rw [Finset.mem_image] at himage
    obtain ⟨f, hfedge, hfe⟩ := himage
    rw [Finset.mem_image]
    exact ⟨f, Finset.mem_filter.mpr ⟨hfedge, hfe ▸ he⟩, hfe⟩

theorem bond_extendInteriorPlus_eq_glue
    (d n : ℕ) (tau : ConfigSpace (StatMech.FK.boxVerts d n))
    (e : Sym2 (StatMech.FK.boxVerts d (n + 1))) :
    bond (extendInteriorPlus (boxCurrentInterior d (n + 1))
        ((boxCurrentInteriorConfigEquiv d n).symm tau)) e =
      bond (glue (plusField d) tau) (StatMech.FK.edgeIncl d (n + 1) e) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [bond_mk, StatMech.FK.edgeIncl, Sym2.map_mk, bond_mk]
      simp only [spin]
      rw [extendInteriorPlus_configEquiv_symm_eq_glue,
        extendInteriorPlus_configEquiv_symm_eq_glue]

theorem edgeSpinSum_boxPullbackEdges
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n)
    (tau : ConfigSpace (StatMech.FK.boxVerts d n)) :
    edgeSpinSum (boxPullbackEdges d n F)
        (extendInteriorPlus (boxCurrentInterior d (n + 1))
          ((boxCurrentInteriorConfigEquiv d n).symm tau)) =
      edgeSpinSum F (glue (plusField d) tau) := by
  unfold edgeSpinSum
  simp_rw [bond_extendInteriorPlus_eq_glue]
  rw [← Finset.sum_image
    (StatMech.FK.edgeIncl_injective d (n + 1)).injOn]
  rw [image_boxPullbackEdges d n F hF]

theorem boltzmannJ_extendInteriorPlus_eq_fvWeight
    (d n : ℕ) (beta : ℝ)
    (tau : ConfigSpace (StatMech.FK.boxVerts d n)) :
    boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
        (extendInteriorPlus (boxCurrentInterior d (n + 1))
          ((boxCurrentInteriorConfigEquiv d n).symm tau)) =
      Real.exp (beta *
          ((Finset.image (StatMech.FK.edgeIncl d (n + 1))
              (StatMech.FK.boxGraph d (n + 1)).edgeFinset) \
            bondFinsetTouch d n).card) *
        fvWeight (plusField d) n (bondFinsetTouch d n) beta 0 tau := by
  calc
    boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
        (extendInteriorPlus (boxCurrentInterior d (n + 1))
          ((boxCurrentInteriorConfigEquiv d n).symm tau)) =
      isingWiredWeight (StatMech.FK.boxGraph d (n + 1))
        (StatMech.FK.boxBoundary d (n + 1)) beta (latToBox d n tau) := by
      unfold boltzmannJ isingWiredWeight
      rw [if_pos (boundaryFixed_latToBox d n tau)]
      congr 1
      apply congrArg (fun x : ℝ => beta * x)
      apply Finset.sum_congr rfl
      intro e he
      simp only [one_mul]
      rw [bond_extendInteriorPlus_eq_glue,
        hbx_isingBond_latToBox_eq]
    _ = _ := hbx_isingWiredWeight_latToBox d n beta tau

theorem boundaryPartitionJ_box_eq_fvZ
    (d n : ℕ) (beta : ℝ) :
    boundaryPartitionJ (StatMech.FK.boxGraph d (n + 1)) beta
        (fun _ => 1) (boxCurrentInterior d (n + 1)) =
      Real.exp (beta *
          ((Finset.image (StatMech.FK.edgeIncl d (n + 1))
              (StatMech.FK.boxGraph d (n + 1)).edgeFinset) \
            bondFinsetTouch d n).card) *
        fvZ (plusField d) n (bondFinsetTouch d n) beta 0 := by
  unfold boundaryPartitionJ fvZ
  rw [← (boxCurrentInteriorConfigEquiv d n).symm.sum_comp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tau htau
  exact boltzmannJ_extendInteriorPlus_eq_fvWeight d n beta tau

theorem boundarySpinExpectation_box_eq_plusIntegral
    (d n : ℕ) (beta : ℝ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) :
    ((∑ s : ConfigSpace ↑(boxCurrentInterior d (n + 1)),
        boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
            (extendInteriorPlus (boxCurrentInterior d (n + 1)) s) *
          Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F)
            (extendInteriorPlus (boxCurrentInterior d (n + 1)) s))) /
      boundaryPartitionJ (StatMech.FK.boxGraph d (n + 1)) beta
        (fun _ => 1) (boxCurrentInterior d (n + 1))) =
      ∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  let C : ℝ :=
    ((Finset.image (StatMech.FK.edgeIncl d (n + 1))
        (StatMech.FK.boxGraph d (n + 1)).edgeFinset \
      bondFinsetTouch d n).card : ℝ)
  let E : ℝ := Real.exp (beta * C)
  have hE0 : E ≠ 0 := (Real.exp_pos _).ne'
  have hnum :
      (∑ s : ConfigSpace ↑(boxCurrentInterior d (n + 1)),
        boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
            (extendInteriorPlus (boxCurrentInterior d (n + 1)) s) *
          Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F)
            (extendInteriorPlus (boxCurrentInterior d (n + 1)) s))) =
        E * ∑ tau : ConfigSpace (StatMech.FK.boxVerts d n),
          fvWeight (plusField d) n (bondFinsetTouch d n) beta 0 tau *
            Real.exp (-beta * edgeSpinSum F (glue (plusField d) tau)) := by
    rw [← (boxCurrentInteriorConfigEquiv d n).symm.sum_comp,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau htau
    rw [boltzmannJ_extendInteriorPlus_eq_fvWeight,
      edgeSpinSum_boxPullbackEdges d n F hF]
    change Real.exp (beta * C) * _ * _ = E * (_ * _)
    rw [← show E = Real.exp (beta * C) from rfl]
    ring
  have hden :
      boundaryPartitionJ (StatMech.FK.boxGraph d (n + 1)) beta
          (fun _ => 1) (boxCurrentInterior d (n + 1)) =
        E * fvZ (plusField d) n (bondFinsetTouch d n) beta 0 := by
    rw [boundaryPartitionJ_box_eq_fvZ]
  rw [hnum, hden, mul_div_mul_left _ _ hE0]
  change _ = ∫ omega, Real.exp (-beta * edgeSpinSum F omega)
    ∂fvMeasure (plusField d) n (bondFinsetTouch d n) beta 0
  rw [integral_fvMeasure_eq_sum]
  unfold fvProb
  rw [Finset.sum_div]
  congr 1
  funext tau
  ring

end StatMech.FrontierB
