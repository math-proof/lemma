/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingFreeStateCoordinateSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionInfinite.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingFreeStateCoordinateSymmetry
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

@[simp] theorem freeBoxAutomorphismEquiv_val
    (e : Site d ≃ Site d)
    (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n)
    (n : Nat) (x : freeDomainVertices (boxFinset d n)) :
    (freeBoxAutomorphismEquiv e hbox n x).1 = e x.1 := rfl

theorem freeDomainSpinSupport_map_freeBoxAutomorphism
    (e : Site d ≃ Site d)
    (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n)
    (n : Nat) (A : Finset (Site d)) :
    (freeDomainSpinSupport (boxFinset d n) A).map
        (freeBoxAutomorphismEquiv e hbox n).toEmbedding =
      freeDomainSpinSupport (boxFinset d n) (A.map e.toEmbedding) := by
  ext z
  simp only [Finset.mem_map, freeDomainSpinSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx, rfl⟩
  · rintro ⟨a, ha, haz⟩
    let x : freeDomainVertices (boxFinset d n) :=
      ⟨a, by
        apply (hbox n a).2
        have haz' : e a = z.1 := haz
        rw [haz']
        exact z.2⟩
    refine ⟨x, ha, ?_⟩
    apply Subtype.ext
    exact haz


theorem integral_freeState_spinProd_boxAutomorphism
    (e : Site d ≃ Site d)
    (hadj : ∀ x y, (hypercubicLattice d).Adj x y ↔
      (hypercubicLattice d).Adj (e x) (e y))
    (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n)
    (beta : Real) (hbeta : 0 <= beta) (A : Finset (Site d)) :
    (∫ omega, spinProd (A.map e.toEmbedding) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  let eA := A.map e.toEmbedding
  let S := A ∪ eA
  obtain ⟨N, hSN⟩ := Lattice.finite_subset_box
    (↑S : Set (Site d)) S.finite_toSet
  have hAbox (n : Nat) (hn : N <= n) : A ⊆ boxFinset d n := by
    intro x hx
    rw [mem_boxFinset]
    exact box_mono d hn (hSN (Finset.mem_union_left eA hx))
  have heAbox (n : Nat) (hn : N <= n) : eA ⊆ boxFinset d n := by
    intro x hx
    rw [mem_boxFinset]
    exact box_mono d hn (hSN (Finset.mem_union_right A hx))
  have hfinite (n : Nat) (hn : N <= n) :
      (∫ omega, spinProd eA omega
          ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) =
        ∫ omega, spinProd A omega
          ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
    rw [integral_freeMeasure_spinProd_eq_freeDomain
        d n beta eA (heAbox n hn),
      integral_freeMeasure_spinProd_eq_freeDomain
        d n beta A (hAbox n hn)]
    let eb := freeBoxAutomorphismEquiv e hbox n
    have hebAdj (x y : freeDomainVertices (boxFinset d n)) :
        (freeDomainGraph (boxFinset d n)).Adj x y ↔
          (freeDomainGraph (boxFinset d n)).Adj (eb x) (eb y) := by
      exact hadj x.1 y.1
    have hrel := isingExpectation_spinProd_relabel
      (freeDomainGraph (boxFinset d n))
      (freeDomainGraph (boxFinset d n)) eb hebAdj beta 0
      (freeDomainSpinSupport (boxFinset d n) A)
    rw [freeDomainSpinSupport_map_freeBoxAutomorphism e hbox n A] at hrel
    exact hrel.symm
  have hlimA := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta A
  have hlimeA := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta eA
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto hlimeA hlimA (by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hfinite n hn).le)
  · exact le_of_tendsto_of_tendsto hlimA hlimeA (by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hfinite n hn).ge)


end StatMech.FrontierA
