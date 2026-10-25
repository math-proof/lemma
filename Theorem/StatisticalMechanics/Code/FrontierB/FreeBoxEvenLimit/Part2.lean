/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Ising.IsingTranslatedBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity.Part2
import Def.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit
open MeasureTheory Filter Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem spinProd_glue_eq_boxSpinSupport
    (d n : ℕ) (A : Finset (Site d))
    (hA : ↑A ⊆ box d n) (tau : ConfigSpace (sctBox d n)) :
    spinProd A (glue (minusField d) tau) =
      spinProd (boxSpinSupport d n A) tau := by
  have hsupp : (boxSpinSupport d n A).image Subtype.val = A := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa [boxSpinSupport] using hy
    · intro hx
      rw [Finset.mem_image]
      let y : sctBox d n := ⟨x, hA hx⟩
      exact ⟨y, by simp [boxSpinSupport, y, hx], rfl⟩
  unfold spinProd
  calc
    (∏ x ∈ A, spin (glue (minusField d) tau) x) =
        ∏ x ∈ (boxSpinSupport d n A).image Subtype.val,
          spin (glue (minusField d) tau) x := by rw [hsupp]
    _ = ∏ x ∈ boxSpinSupport d n A,
          spin (glue (minusField d) tau) x.1 := by
      rw [Finset.prod_image Subtype.val_injective.injOn]
    _ = ∏ x ∈ boxSpinSupport d n A, spin tau x := by
      apply Finset.prod_congr rfl
      intro x hx
      simp [spin, glue, x.2]

theorem integral_freeMeasure_spinProd
    (d n : ℕ) (beta h : ℝ) (A : Finset (Site d))
    (hA : ↑A ⊆ box d n) :
    ∫ omega, spinProd A omega
        ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d))) =
      isingExpectation (sctBoxGraph d n) beta h
        (spinProd (boxSpinSupport d n A)) := by
  change (∫ omega, spinProd A omega
    ∂(fvMeasure (minusField d) n (bondFinsetInternal d n) beta h)) = _
  rw [integral_fvMeasure_eq_sum]
  unfold isingExpectation
  apply Finset.sum_congr rfl
  intro tau htau
  rw [sct_fvProb_eq_isingProb]
  congr 1
  exact spinProd_glue_eq_boxSpinSupport d n A hA tau

theorem boxSpinSupport_map_inclusion
    (d : ℕ) {n m : ℕ} (hnm : n ≤ m) (A : Finset (Site d))
    (hA : ↑A ⊆ box d n) :
    ((boxSpinSupport d n A).map
        (sctBoxInclusionEquiv d hnm).toEmbedding).map
        (Function.Embedding.subtype (sctBoxInLarger d n m)) =
      boxSpinSupport d m A := by
  ext z
  simp only [Finset.mem_map, boxSpinSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact hx
  · intro hz
    let x : sctBox d n := ⟨z.1, hA hz⟩
    let w : {z : sctBox d m // sctBoxInLarger d n m z} :=
      sctBoxInclusionEquiv d hnm x
    refine ⟨w, ⟨x, ?_, rfl⟩, ?_⟩
    · exact hz
    · apply Subtype.ext
      rfl

theorem isingExpectation_boxSpinSupport_mono
    (d : ℕ) {n m : ℕ} (hnm : n ≤ m) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : Finset (Site d)) (hA : ↑A ⊆ box d n) :
    isingExpectation (sctBoxGraph d n) beta 0
        (spinProd (boxSpinSupport d n A)) ≤
      isingExpectation (sctBoxGraph d m) beta 0
        (spinProd (boxSpinSupport d m A)) := by
  let e := sctBoxInclusionEquiv d hnm
  calc
    isingExpectation (sctBoxGraph d n) beta 0
        (spinProd (boxSpinSupport d n A)) =
        isingExpectation
          ((sctBoxGraph d m).comap
            (Subtype.val :
              {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m)) beta 0
          (spinProd ((boxSpinSupport d n A).map e.toEmbedding)) := by
      exact isingExpectation_spinProd_relabel (sctBoxGraph d n)
        ((sctBoxGraph d m).comap
          (Subtype.val :
            {z : sctBox d m // sctBoxInLarger d n m z} → sctBox d m))
        e (sctBoxInclusionEquiv_adj d hnm) beta 0 (boxSpinSupport d n A)
    _ ≤ isingExpectation (sctBoxGraph d m) beta 0
          (spinProd (((boxSpinSupport d n A).map e.toEmbedding).map
            (Function.Embedding.subtype (sctBoxInLarger d n m)))) :=
      isingExpectation_spinProd_induce_le (sctBoxGraph d m)
        (sctBoxInLarger d n m) beta 0 hbeta (le_refl 0) _
    _ = isingExpectation (sctBoxGraph d m) beta 0
          (spinProd (boxSpinSupport d m A)) := by
      rw [boxSpinSupport_map_inclusion d hnm A hA]

theorem isingExpectation_spinProd_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (beta h : ℝ) (A : Finset V) :
    isingExpectation G beta h (spinProd A) ≤ 1 := by
  unfold isingExpectation
  calc
    (∑ s : ConfigSpace V, isingProb G beta h s * spinProd A s) ≤
        ∑ s : ConfigSpace V, isingProb G beta h s * 1 := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (spinProd_le_one A s)
        (isingProb_nonneg G beta h s)
    _ = 1 := by simp [isingProb_sum_eq_one]

theorem continuous_spinProd {d : ℕ} (A : Finset (Site d)) :
    Continuous (spinProd A : ConfigSpace (Site d) → ℝ) := by
  classical
  induction A using Finset.induction with
  | empty => simpa [spinProd] using
      (continuous_const : Continuous (fun _ : ConfigSpace (Site d) => (1 : ℝ)))
  | @insert x A hx ih =>
      rw [show spinProd (insert x A) =
          fun omega => spin omega x * spinProd A omega by
        funext omega
        simp [spinProd, hx]]
      exact (continuous_spin_apply x).mul ih

end StatMech.FrontierB
