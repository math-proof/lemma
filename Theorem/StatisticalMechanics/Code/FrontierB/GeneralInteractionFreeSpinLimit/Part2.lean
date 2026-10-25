/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit.Part2
open Filter Topology Set
open scoped BigOperators
open Finset


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Sharpness StatMech.Lattice


theorem interactionBoxSpinSupport_map_inclusion (d : Nat) {n m : Nat}
    (hnm : n ≤ m) (A : Finset (Site d)) (hA : (A : Set (Site d)) ⊆ box d n) :
    (interactionBoxSpinSupport d n A).map
        (interactionBoxVertexIncl d hnm) =
      interactionBoxSpinSupport d m A := by
  ext x
  simp only [Finset.mem_map, interactionBoxSpinSupport,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    let y : interactionBoxVertices d n :=
      ⟨x.1, mem_interactionBoxVertices.mpr (hA hx)⟩
    refine ⟨y, ?_, ?_⟩
    · exact hx
    · apply Subtype.ext
      rfl


theorem expJ_spinProd_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (K : Sym2 V → ℝ) (hf : V → ℝ)
    (A : Finset V) : expJ E K hf (spinProd A) ≤ 1 := by
  unfold expJ
  apply (div_le_one (ZJ_pos E K hf)).2
  unfold ZJ
  apply Finset.sum_le_sum
  intro s hs
  simpa using mul_le_mul_of_nonneg_right (spinProd_le_one A s)
    (wJ_nonneg E K hf s)


theorem generalInteractionBox_fixed_spinProd_mono {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta) {n m : Nat} (hnm : n ≤ m)
    (A : Finset (Site d)) (hA : (A : Set (Site d)) ⊆ box d n) :
    expJ (interactionBoxGraph d n).edgeFinset
        (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
        (spinProd (interactionBoxSpinSupport d n A)) ≤
      expJ (interactionBoxGraph d m).edgeFinset
        (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0)
        (spinProd (interactionBoxSpinSupport d m A)) := by
  rw [← interactionBoxSpinSupport_map_inclusion d hnm A hA]
  exact generalInteractionBox_spinProd_mono J hJ beta hbeta hnm
    (interactionBoxSpinSupport d n A)


theorem generalInteractionBox_spinProd_tendsto {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta) (A : Finset (Site d)) :
    ∃ L : ℝ, Tendsto
      (fun n =>
        expJ (interactionBoxGraph d n).edgeFinset
          (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
          (spinProd (interactionBoxSpinSupport d n A)))
      atTop (nhds L) := by
  let a : Nat → ℝ := fun n =>
    expJ (interactionBoxGraph d n).edgeFinset
      (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
      (spinProd (interactionBoxSpinSupport d n A))
  obtain ⟨N, hAN⟩ := finite_subset_box (A : Set (Site d)) A.finite_toSet
  have hA_add (k : Nat) : (A : Set (Site d)) ⊆ box d (k + N) :=
    hAN.trans (box_mono d (Nat.le_add_left N k))
  have htail_mono : Monotone (fun k => a (k + N)) := by
    intro k l hkl
    exact generalInteractionBox_fixed_spinProd_mono J hJ beta hbeta
      (Nat.add_le_add_right hkl N) A (hA_add k)
  have htail_bdd : BddAbove (Set.range (fun k => a (k + N))) := by
    refine ⟨1, ?_⟩
    rintro y ⟨k, rfl⟩
    exact expJ_spinProd_le_one (interactionBoxGraph d (k + N)).edgeFinset
      (fun e => beta * interactionBoxCoupling J (k + N) e) (fun _ => 0)
      (interactionBoxSpinSupport d (k + N) A)
  let L : ℝ := ⨆ k, a (k + N)
  have htail : Tendsto (fun k => a (k + N)) atTop (nhds L) := by
    simpa only [L] using tendsto_atTop_ciSup htail_mono htail_bdd
  refine ⟨L, ?_⟩
  exact (tendsto_add_atTop_iff_nat N).1 htail

end StatMech.FrontierB
