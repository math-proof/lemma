/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part4
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem pottsIID_blockLabels_law
    {κ ι : Type*} [DecidableEq ι] {q : Nat} [NeZero q]
    (F : κ -> Finset ι)
    (hdisjoint : ∀ k l, k ≠ l -> Disjoint (F k) (F l)) :
    Measure.map (pottsBlockLabels F)
        (Measure.infinitePi fun _ : ι =>
          (PMF.uniformOfFintype (Fin q)).toMeasure) =
      Measure.infinitePi fun k : κ =>
        Measure.infinitePi fun _ : F k =>
          (PMF.uniformOfFintype (Fin q)).toMeasure := by
  let embed : ((k : κ) × F k) -> ι := fun p => p.2
  have hembed : Function.Injective embed := by
    rintro ⟨k, x⟩ ⟨l, y⟩ hxy
    change (x : ι) = (y : ι) at hxy
    have hkl : k = l := by
      by_contra hne
      have hx : (x : ι) ∈ F k := x.2
      have hy : (x : ι) ∈ F l := by rw [hxy]; exact y.2
      exact Finset.disjoint_left.mp (hdisjoint k l hne) hx hy
    subst l
    simp_all
  have hflat : Measure.map (fun label : ι -> Fin q =>
        fun p : ((k : κ) × F k) => label (embed p))
      (Measure.infinitePi fun _ : ι =>
        (PMF.uniformOfFintype (Fin q)).toMeasure) =
      Measure.infinitePi fun _ : ((k : κ) × F k) =>
        (PMF.uniformOfFintype (Fin q)).toMeasure := by
    simpa using (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) hembed)
  have hfactor : pottsBlockLabels F =
      (MeasurableEquiv.piCurry (fun _ : κ => fun _ : F _ => Fin q)) ∘
        (fun label : ι -> Fin q =>
          fun p : ((k : κ) × F k) => label (embed p)) := by
    funext label k x
    rfl
  rw [hfactor, ← Measure.map_map
    (MeasurableEquiv.piCurry (fun _ : κ => fun _ : F _ => Fin q)).measurable
    (measurable_pi_lambda _ fun p => measurable_pi_apply (embed p)), hflat]
  rw [← Measure.infinitePi_map_piCurry_symm
    (fun _ : κ => fun _ : F _ =>
      (PMF.uniformOfFintype (Fin q)).toMeasure)]
  rw [Measure.map_map]
  · simp
  · exact (MeasurableEquiv.piCurry
      (fun _ : κ => fun _ : F _ => Fin q)).measurable
  · exact (MeasurableEquiv.piCurry
      (fun _ : κ => fun _ : F _ => Fin q)).symm.measurable


theorem pottsIID_blockSums_law
    {κ ι : Type*} [DecidableEq ι] {q : Nat} [NeZero q]
    (F : κ -> Finset ι) (hF : ∀ k, (F k).Nonempty)
    (hdisjoint : ∀ k l, k ≠ l -> Disjoint (F k) (F l)) :
    Measure.map (pottsBlockSums F)
        (Measure.infinitePi fun _ : ι =>
          (PMF.uniformOfFintype (Fin q)).toMeasure) =
      Measure.infinitePi fun _ : κ =>
        (PMF.uniformOfFintype (Fin q)).toMeasure := by
  have hfactor : pottsBlockSums F =
      (fun block : ∀ k, F k -> Fin q => fun k => ∑ x, block k x) ∘
        pottsBlockLabels F := by
    rfl
  rw [hfactor]
  calc
    Measure.map
        ((fun block : ∀ k, F k -> Fin q => fun k => ∑ x, block k x) ∘
          pottsBlockLabels F)
        (Measure.infinitePi fun _ : ι =>
          (PMF.uniformOfFintype (Fin q)).toMeasure) =
      Measure.map (fun block : ∀ k, F k -> Fin q =>
          fun k => ∑ x, block k x)
        (Measure.map (pottsBlockLabels F)
          (Measure.infinitePi fun _ : ι =>
            (PMF.uniformOfFintype (Fin q)).toMeasure)) := by
      have houter : Measurable (fun block : ∀ k, F k -> Fin q =>
          fun k => ∑ x, block k x) :=
        measurable_pi_lambda _ fun k =>
          Finset.univ.measurable_fun_sum fun x _ =>
            (measurable_pi_apply x).comp (measurable_pi_apply k)
      have hinner : Measurable (pottsBlockLabels F :
          (ι -> Fin q) -> ∀ k, F k -> Fin q) := by
        unfold pottsBlockLabels
        exact measurable_pi_lambda _ fun _ =>
          measurable_pi_lambda _ fun x => measurable_pi_apply (x : ι)
      exact (Measure.map_map houter hinner).symm
    _ = Measure.map (fun block : ∀ k, F k -> Fin q =>
          fun k => ∑ x, block k x)
        (Measure.infinitePi fun k : κ =>
          Measure.infinitePi fun _ : F k =>
            (PMF.uniformOfFintype (Fin q)).toMeasure) := by
      rw [pottsIID_blockLabels_law F hdisjoint]
    _ = Measure.infinitePi fun _ : κ =>
        (PMF.uniformOfFintype (Fin q)).toMeasure := by
      rw [Measure.infinitePi_map_pi
        (fun k : κ => Measure.infinitePi fun _ : F k =>
          (PMF.uniformOfFintype (Fin q)).toMeasure)
        (fun k => Finset.univ.measurable_fun_sum fun x _ => measurable_pi_apply x)]
      congrm Measure.infinitePi fun k => ?_
      letI : Nonempty (F k) := by
        obtain ⟨x, hx⟩ := hF k
        exact ⟨⟨x, hx⟩⟩
      rw [Measure.infinitePi_eq_pi]
      exact pottsUniformPi_sum_map


end StatMech.FK
