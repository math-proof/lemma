/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempVertexField.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonPlusLimit.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Def.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
open Finset SimpleGraph MeasureTheory
open scoped BigOperators Classical


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


@[simp] theorem mem_sitesInVolume {Lambda T : Finset (Site d)}
    {x : {v // v ∈ Lambda}} :
    x ∈ sitesInVolume Lambda T ↔ x.1 ∈ T := by
  simp [sitesInVolume]


theorem plusBoundaryField_eq_zero_of_neighbors
    (Lambda T : Finset (Site d))
    (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ Lambda)
    (x : {v // v ∈ Lambda}) (hx : x ∈ sitesInVolume Lambda T) :
    plusBoundaryField Lambda x = 0 := by
  unfold plusBoundaryField
  rw [Nat.cast_eq_zero, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro e he hxe
  rw [plusBoundaryEdges, Finset.mem_filter] at he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hadj : (hypercubicLattice d).Adj a b :=
        gv_bondTouch_subset_edgeSet Lambda s(a, b) he.1
      rw [Sym2.mem_iff] at hxe
      apply he.2
      intro v hv
      rw [Sym2.mem_iff] at hv
      rcases hxe with hxa | hxb
      · have haT : a ∈ T := by simpa [hxa] using hx
        have hbL := hnbr a haT b hadj
        rcases hv with rfl | rfl
        · simpa [hxa] using x.2
        · exact hbL
      · have hbT : b ∈ T := by simpa [hxb] using hx
        have haL := hnbr b hbT a hadj.symm
        rcases hv with rfl | rfl
        · exact haL
        · simpa [hxb] using x.2


theorem gvPlus_simon_subtype
    (Lambda T : Finset (Site d)) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ Lambda)
    (o z : {v // v ∈ Lambda})
    (ho : o.1 ∈ T) (hz : z.1 ∉ T) :
    (∫ omega, spin omega o.1 * spin omega z.1
        ∂(gvPlusMeasure Lambda beta 0)) ≤
      ∑ x ∈ sitesInVolume Lambda T,
        ∑ y ∈ (Finset.univ \ sitesInVolume Lambda T),
          Real.tanh
              (beta * unitEdgeCoupling (graphS d Lambda) s(x, y)) *
            twoPointJ (graphS d Lambda) beta
              (couplingIn (unitEdgeCoupling (graphS d Lambda))
                (sitesInVolume Lambda T)) o x *
            (∫ omega, spin omega y.1 * spin omega z.1
              ∂(gvPlusMeasure Lambda beta 0)) := by
  rw [gvPlus_pair_eq_vertexField]
  have hfield : ∀ x ∈ sitesInVolume Lambda T,
      plusBoundaryField Lambda x = 0 :=
    plusBoundaryField_eq_zero_of_neighbors Lambda T hnbr
  have hsimon := vertexFieldTwoPoint_simon_finite (graphS d Lambda) beta
    (unitEdgeCoupling (graphS d Lambda)) (plusBoundaryField Lambda)
    hbeta (unitEdgeCoupling_nonneg (graphS d Lambda))
    (plusBoundaryField_nonneg Lambda) (sitesInVolume Lambda T) hfield
    o z (by simpa using ho) (by simpa using hz)
  simpa only [gvPlus_pair_eq_vertexField] using hsimon

theorem plusCutSites_sitesInVolume (Lambda T : Finset (Site d))
    (hsub : T ⊆ Lambda) :
    plusCutSites (sitesInVolume Lambda T) = T := by
  ext x
  constructor
  · intro hx
    rw [plusCutSites, Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr
      ⟨⟨x, hsub hx⟩, by simpa using hx, rfl⟩


theorem gvPlus_simon_ambient
    (Lambda T : Finset (Site d)) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsub : T ⊆ Lambda)
    (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y → y ∈ Lambda)
    (ho : Percolation.origin d ∈ T) (z : Site d)
    (hzL : z ∈ Lambda) (hzT : z ∉ T) :
    (∫ omega, spin omega (Percolation.origin d) * spin omega z
        ∂(gvPlusMeasure Lambda beta 0)) ≤
      simonBoundaryIntegral beta T (Percolation.origin d) z
        (gvPlusMeasure Lambda beta 0) := by
  classical
  let oL : {v // v ∈ Lambda} := ⟨Percolation.origin d, hsub ho⟩
  let zL : {v // v ∈ Lambda} := ⟨z, hzL⟩
  let C := (sitesInVolume Lambda T) ×ˢ
    ((Finset.univ : Finset {v // v ∈ Lambda}) \ sitesInVolume Lambda T)
  let A := C.filter (fun p ↦ (graphS d Lambda).Adj p.1 p.2)
  let F : {v // v ∈ Lambda} × {v // v ∈ Lambda} → ℝ := fun p ↦
    Real.tanh (beta * unitEdgeCoupling (graphS d Lambda) s(p.1, p.2)) *
      twoPointJ (graphS d Lambda) beta
        (couplingIn (unitEdgeCoupling (graphS d Lambda))
          (sitesInVolume Lambda T)) oL p.1 *
      (∫ omega, spin omega p.2.1 * spin omega z
        ∂(gvPlusMeasure Lambda beta 0))
  have hs := gvPlus_simon_subtype Lambda T beta hbeta hnbr oL zL
    (by simpa [oL] using ho) (by simpa [zL] using hzT)
  have hdouble :
      (∑ x ∈ sitesInVolume Lambda T,
        ∑ y ∈ (Finset.univ \ sitesInVolume Lambda T), F (x, y)) =
        ∑ p ∈ A, F p := by
    rw [← Finset.sum_product]
    change (∑ p ∈ C, F p) = ∑ p ∈ C.filter _ , F p
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hadj : (graphS d Lambda).Adj p.1 p.2
    · rw [if_pos hadj]
    · rw [if_neg hadj]
      have hzero : unitEdgeCoupling (graphS d Lambda) s(p.1, p.2) = 0 := by
        rw [unitEdgeCoupling, if_neg]
        simpa [SimpleGraph.mem_edgeSet] using hadj
      simp [F, hzero]
  have hboundary :
      (∑ p ∈ A, F p) =
        ∑ e ∈ boundaryEdges d T,
          Real.tanh beta * corrOriginInner d beta T e.1 *
            (∫ omega, spin omega e.2 * spin omega z
              ∂(gvPlusMeasure Lambda beta 0)) := by
    symm
    apply Finset.sum_bij
      (fun e he ↦
        (⟨e.1, hsub (shk_mem_boundaryEdges_iff.mp he).1⟩,
         ⟨e.2, hnbr e.1 (shk_mem_boundaryEdges_iff.mp he).1 e.2
            (shk_mem_boundaryEdges_iff.mp he).2.2⟩))
    · intro e he
      obtain ⟨he1, he2, hadj⟩ := shk_mem_boundaryEdges_iff.mp he
      simp only [A, Finset.mem_filter, C, Finset.mem_product]
      exact ⟨⟨by simpa using he1, by simpa using he2⟩, hadj⟩
    · intro a ha b hb hab
      exact Prod.ext
        (congrArg (fun p ↦ p.1.1) hab)
        (congrArg (fun p ↦ p.2.1) hab)
    · intro p hp
      simp only [A, Finset.mem_filter, C, Finset.mem_product] at hp
      refine ⟨(p.1.1, p.2.1), ?_, ?_⟩
      · apply shk_mem_boundaryEdges_iff.mpr
        exact ⟨by simpa using hp.1.1, by simpa using hp.1.2, hp.2⟩
      · apply Prod.ext <;> rfl
    · intro e he
      obtain ⟨he1, he2, hadj⟩ := shk_mem_boundaryEdges_iff.mp he
      have hedge : unitEdgeCoupling (graphS d Lambda)
          s(⟨e.1, hsub he1⟩,
            ⟨e.2, hnbr e.1 he1 e.2 hadj⟩) = 1 := by
        rw [unitEdgeCoupling, if_pos]
        exact hadj
      have hlocal := plus_localCorr_eq_corrOriginInner Lambda beta
        (sitesInVolume Lambda T)
        (o := oL) (x := ⟨e.1, hsub he1⟩)
        (by simpa [oL] using ho) (by simpa using he1) rfl
      rw [plusCutSites_sitesInVolume Lambda T hsub] at hlocal
      simp [F, hedge, hlocal]
  rw [hdouble, hboundary] at hs
  simpa [F, oL, zL, simonBoundaryIntegral] using hs


theorem plusMeasure_simon_box
    (n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (hsub : T ⊆ boxFinset d n)
    (hnbr : ∀ x ∈ T, ∀ y, (hypercubicLattice d).Adj x y →
      y ∈ boxFinset d n)
    (ho : Percolation.origin d ∈ T) (z : Site d)
    (hzL : z ∈ boxFinset d n) (hzT : z ∉ T) :
    (∫ omega, spin omega (Percolation.origin d) * spin omega z
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) ≤
      simonBoundaryIntegral beta T (Percolation.origin d) z
        (plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
  rw [← iptp_gvPlusMeasure_eq_plusMeasure]
  exact gvPlus_simon_ambient (boxFinset d n) T beta hbeta hsub hnbr
    ho z hzL hzT


theorem plusMeasure_simon_eventually
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : Percolation.origin d ∈ T)
    (z : Site d) (hzT : z ∉ T) (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ∀ᶠ n in Filter.atTop,
      (∫ omega, spin omega (Percolation.origin d) * spin omega z
        ∂(plusMeasure d (phi n) beta 0 : Measure (ConfigSpace (Site d)))) ≤
      simonBoundaryIntegral beta T (Percolation.origin d) z
        (plusMeasure d (phi n) beta 0 : Measure (ConfigSpace (Site d))) := by
  classical
  let U : Finset (Site d) := insert z (gvCand T)
  obtain ⟨R, hR⟩ := finite_subset_box (U : Set (Site d)) U.finite_toSet
  filter_upwards
    [hphi.tendsto_atTop.eventually (Filter.eventually_ge_atTop R)] with n hn
  have hU (w : Site d) (hw : w ∈ U) : w ∈ boxFinset d (phi n) := by
    rw [mem_boxFinset, mem_box]
    intro i
    exact (hR (by simpa using hw) i).trans hn
  apply plusMeasure_simon_box (phi n) beta hbeta T
  · intro x hx
    apply hU x
    change x ∈ insert z (gvCand T)
    simp only [Finset.mem_insert]
    right
    rw [gvCand, Finset.mem_biUnion]
    exact ⟨x, hx, gv_self_mem_ball x⟩
  · intro x hx y hadj
    apply hU y
    change y ∈ insert z (gvCand T)
    simp only [Finset.mem_insert]
    right
    rw [gvCand, Finset.mem_biUnion]
    exact ⟨x, hx, gv_nbr_mem_ball hadj⟩
  · exact ho
  · exact hU z (Finset.mem_insert_self z _)
  · exact hzT


theorem plusCorr_simon
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : Percolation.origin d ∈ T)
    (z : Site d) (hzT : z ∉ T) :
    plusCorr d beta (Percolation.origin d) z ≤
      simonBoundaryPlus beta T (Percolation.origin d) z := by
  apply plusCorr_simon_of_eventually_finite
  intro phi hphi
  exact plusMeasure_simon_eventually beta hbeta T ho z hzT phi hphi

end Sharpness
end StatMech
