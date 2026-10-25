/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeParityErrorVanishing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part3
import Def.StatisticalMechanics.Code.FrontierB.FreeParityErrorVanishing
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

theorem inverseAxisTranslateFinset_eventually_outside_box
    (hd : 1 ≤ d) (B : Finset (Site d)) (m : Nat) :
    ∀ᶠ n in atTop, (inverseAxisTranslateFinset hd n B : Set (Site d)) ⊆
      (box d m)ᶜ := by
  let M := B.sup fun x => (x ⟨0, hd⟩).natAbs
  filter_upwards [eventually_ge_atTop (M + m + 1)] with n hn
  intro z hz
  simp only [inverseAxisTranslateFinset, Finset.coe_image, Set.mem_image,
    Finset.mem_coe] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [Set.mem_compl_iff]
  intro hbox
  have hxBound : x ⟨0, hd⟩ ≤ (M : Int) := by
    exact (Int.le_natAbs.trans (by exact_mod_cast
      (Finset.le_sup (f := fun x => (x ⟨0, hd⟩).natAbs) hx)))
  have hcoord := hbox ⟨0, hd⟩
  have hval :
      (((FK.freeAxisTranslationPower hd n)⁻¹ • x) ⟨0, hd⟩) =
        x ⟨0, hd⟩ - n := by
    change (-(Multiplicative.toAdd (FK.freeAxisTranslationPower hd n)) + x)
      ⟨0, hd⟩ = _
    simp [FK.freeAxisTranslationPower]
    ring
  rw [hval] at hcoord
  have hneg : x ⟨0, hd⟩ - (n : Int) ≤ -(m + 1 : Int) := by omega
  have habs : ((x ⟨0, hd⟩ - (n : Int)).natAbs : Int) =
      -(x ⟨0, hd⟩ - (n : Int)) := by
    rw [← Int.natAbs_neg, Int.natAbs_of_nonneg]
    omega
  have hcoord' : ((x ⟨0, hd⟩ - (n : Int)).natAbs : Int) ≤ m := by
    exact_mod_cast hcoord
  rw [habs] at hcoord'
  omega


theorem twoOddCrossClusters_axisTranslate_real_tendsto_zero
    (hd : 1 ≤ d)
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0)
    (A B : Finset (Site d)) :
    Tendsto (fun n => (mu : Measure _).real
      (twoOddCrossClustersEvent (hypercubicLattice d) A
        (inverseAxisTranslateFinset hd n B))) atTop (nhds 0) := by
  have hsum : Tendsto (fun m => ∑ x ∈ A, ∑ y ∈ A,
      (mu : Measure _).real (twoArmDisconnectedTraceEvent m x y))
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum A (fun x hx =>
      tendsto_finsetSum A (fun y hy =>
        twoArmDisconnectedTraceEvent_real_tendsto_zero mu hunique x y))
  obtain ⟨R, hAR⟩ := Percolation.finite_subset_box
    (A : Set (Site d)) A.finite_toSet
  rw [Metric.tendsto_atTop] at hsum ⊢
  intro epsilon hepsilon
  obtain ⟨M, hM⟩ := hsum epsilon hepsilon
  let m := max M (R + 1)
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hAbox : (A : Set (Site d)) ⊆ box d (m - 1) := by
    apply hAR.trans
    apply box_mono d
    dsimp [m]
    omega
  have hsmall : ∑ x ∈ A, ∑ y ∈ A,
      (mu : Measure _).real (twoArmDisconnectedTraceEvent m x y) < epsilon := by
    have hdist := hM m (by dsimp [m]; omega)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (Finset.sum_nonneg fun x hx =>
        Finset.sum_nonneg fun y hy => measureReal_nonneg)] at hdist
    exact hdist
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (inverseAxisTranslateFinset_eventually_outside_box hd B (m - 1))
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hsubset := twoOddCrossClustersEvent_subset_twoArmUnion m hm A
    (inverseAxisTranslateFinset hd n B) hAbox (hN n hn)
  have hfinite : (mu : Measure (ConfigSpace (Sym2 (Site d))))
      (⋃ x ∈ A, ⋃ y ∈ A, twoArmDisconnectedTraceEvent m x y) ≠ ⊤ :=
    measure_ne_top (mu : Measure (ConfigSpace (Sym2 (Site d)))) _
  calc
    (mu : Measure _).real
        (twoOddCrossClustersEvent (hypercubicLattice d) A
          (inverseAxisTranslateFinset hd n B)) ≤
      (mu : Measure _).real
        (⋃ x ∈ A, ⋃ y ∈ A, twoArmDisconnectedTraceEvent m x y) :=
      measureReal_mono (μ := (mu : Measure _)) hsubset
        (by exact hfinite)
    _ ≤ ∑ x ∈ A, (mu : Measure _).real
        (⋃ y ∈ A, twoArmDisconnectedTraceEvent m x y) :=
      measureReal_biUnion_finset_le A _
    _ ≤ ∑ x ∈ A, ∑ y ∈ A,
        (mu : Measure _).real (twoArmDisconnectedTraceEvent m x y) :=
      Finset.sum_le_sum fun x hx => measureReal_biUnion_finset_le A _
    _ < epsilon := hsmall

end StatMech.FrontierB
