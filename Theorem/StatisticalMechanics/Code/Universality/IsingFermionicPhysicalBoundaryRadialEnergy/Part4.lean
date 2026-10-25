/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryRadialPatchCellDiagonalVariation_eq_cellDarts
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (c : FKIsingSquareRadialPatchInteriorCell m) :
    fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
        n m hn hm hm2 c =
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm
            (fkIsingSquareRadialPatchCellPrimalDart n m hm c).snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm
            (fkIsingSquareRadialPatchCellPrimalDart n m hm c).fst| +
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2
            (fkIsingSquareRadialPatchCellDualDart m c).snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2
            (fkIsingSquareRadialPatchCellDualDart m c).fst| := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · have h11 : Even ((c.1.1 + 1) + (c.2.1 + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp h
      omega
    have h10 : ¬ Even ((c.1.1 + 1) + c.2.1) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp h
      omega
    have h01 : ¬ Even (c.1.1 + (c.2.1 + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp h
      omega
    simp [fkIsingSquareBoundaryRadialPatchCellDiagonalVariation,
      fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead,
      fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue,
      h, h11, h10, h01]
  · have h11 : ¬ Even ((c.1.1 + 1) + (c.2.1 + 1)) := by
      rw [Nat.not_even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega
    have h10 : Even ((c.1.1 + 1) + c.2.1) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega
    have h01 : Even (c.1.1 + (c.2.1 + 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega
    simp [fkIsingSquareBoundaryRadialPatchCellDiagonalVariation,
      fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead,
      fkIsingSquareBoundaryRadialPatchFullValue,
      fkIsingSquareRadialPatchFullValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue,
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue,
      h, h11, h10, h01]
    rw [add_comm]
    congr 1
    exact abs_sub_comm _ _

theorem fkIsingSquareBoundaryRadialPatch_normSq_full_le_cellDiagonalVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (c : FKIsingSquareRadialPatchInteriorCell m) :
    Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩) ≤
      2 * fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
        n m hn hm hm2 c := by
  exact fkIsingSquareBoundaryRadialPatch_normSq_full_le_diagonalVariation
    n m hn hm hm2 c.1.1 c.2.1 (by omega) (by omega)


theorem fkIsingSquareBoundaryRadialPatch_deepCellDiagonalVariation_sum_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) :
    (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
          n m hn hm hm2 c) ≤
      (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts
          n m hm (by omega) r,
        |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
              n m hn hm d.snd -
          FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
              n m hn hm d.fst|) +
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
              n m hn hm hm2 d.snd -
          FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
              n m hn hm hm2 d.fst| := by
  classical
  let C := fkIsingSquareRadialPatchDeepCells n m hm hm2 r
  let Sp := fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r
  let Sd := fkIsingSquareRadialPatchDualDeepDarts m hm2 r
  let pd := fkIsingSquareRadialPatchCellPrimalDart n m hm
  let dd := fkIsingSquareRadialPatchCellDualDart m
  let fp := fun d : (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart ↦
    |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
          n m hn hm d.snd -
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
          n m hn hm d.fst|
  let fd := fun d : (fkIsingSquareRadialPatchDualGraph m).Dart ↦
    |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
          n m hn hm hm2 d.snd -
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
          n m hn hm hm2 d.fst|
  have hpInject : Set.InjOn pd (C : Set _) :=
    (fkIsingSquareRadialPatchCellPrimalDart_injective n m hm).injOn
  have hdInject : Set.InjOn dd (C : Set _) :=
    (fkIsingSquareRadialPatchCellDualDart_injective m).injOn
  have hpSubset : C.image pd ⊆ Sp := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hc).2.1
  have hdSubset : C.image dd ⊆ Sd := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hc).2.2
  have hpSum : (∑ c ∈ C, fp (pd c)) ≤ ∑ d ∈ Sp, fp d := by
    rw [← Finset.sum_image hpInject]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpSubset
      (fun d _ _ ↦ abs_nonneg _)
  have hdSum : (∑ c ∈ C, fd (dd c)) ≤ ∑ d ∈ Sd, fd d := by
    rw [← Finset.sum_image hdInject]
    exact Finset.sum_le_sum_of_subset_of_nonneg hdSubset
      (fun d _ _ ↦ abs_nonneg _)
  simp_rw [fkIsingSquareBoundaryRadialPatchCellDiagonalVariation_eq_cellDarts
    n m hn hm hm2]
  change (∑ c ∈ C, (fp (pd c) + fd (dd c))) ≤ _
  rw [Finset.sum_add_distrib]
  exact add_le_add hpSum hdSum


theorem fkIsingSquareBoundaryRadialPatch_deepCell_normSq_sum_le_variation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) :
    (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        Complex.normSq
          (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤
      2 *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts
            n m hm (by omega) r,
          |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
                n m hn hm d.snd -
            FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
                n m hn hm d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
                n m hn hm hm2 d.snd -
            FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
                n m hn hm hm2 d.fst|) := by
  calc
    _ ≤ ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        2 * fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
          n m hn hm hm2 c := by
      apply Finset.sum_le_sum
      intro c hc
      exact fkIsingSquareBoundaryRadialPatch_normSq_full_le_cellDiagonalVariation
        n m hn hm hm2 c
    _ = 2 * (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        fkIsingSquareBoundaryRadialPatchCellDiagonalVariation
          n m hn hm hm2 c) := by simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (fkIsingSquareBoundaryRadialPatch_deepCellDiagonalVariation_sum_le
        n m hn hm hm2 r) (by norm_num)


theorem fkIsingSquareBoundaryRadialPatchWindowCarrier_normalized_normSq_le
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (p : IsingLeapfrogBox R) :
    Complex.normSq
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).normalizedFermionicObservable
          mesh
          (fkIsingSquareRadialPatchWindowCarrier
            n m baseI baseJ R hm hfitI hfitJ p)) ≤
      Complex.normSq
        (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨baseI + p.1.1, by have := p.1.2; omega⟩
              ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ /
          (Real.sqrt (2 * mesh) : Complex)) := by
  let i : Fin m := ⟨baseI + p.1.1, by have := p.1.2; omega⟩
  let j : Fin m := ⟨baseJ + p.2.1, by have := p.2.2; omega⟩
  let e := fkIsingSquareRadialPatchEdge n m hm i j
  let F := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j
  let t := fkIsingSquareWiredDirectedTangent n hn (.dart (e, .west))
  have ht : Complex.normSq t = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [t, fkIsingSquareWiredDirectedTangent, Complex.norm_exp]
  have hproj : Complex.normSq (isingProj t F) ≤ Complex.normSq F := by
    have hpair := isingProj_normSq_add_neg t F ht
    have hnonneg := Complex.normSq_nonneg (isingProj (-t) F)
    linarith
  have hobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .west)) = isingProj t F := by
    exact (fkIsingSquareBoundaryRadialPatchFullObservable_projection
      n m hn hm i j .west).symm
  have hsqrt : 0 < Real.sqrt (2 * mesh) := Real.sqrt_pos.2 (by positivity)
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt, Real.sq_sqrt (by positivity)]
  change Complex.normSq
      ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .west)) /
        (Real.sqrt (2 * mesh) : Complex)) ≤
    Complex.normSq (F / (Real.sqrt (2 * mesh) : Complex))
  rw [hobs, hnorm, hnorm]
  exact div_le_div_of_nonneg_right hproj (by positivity)

end
end StatMech.Universality
