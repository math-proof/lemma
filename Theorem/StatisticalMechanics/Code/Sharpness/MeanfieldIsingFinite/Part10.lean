/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part10
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


theorem mem_sctExternalBoxPairs {d n : ℕ} {p : sctBox d n × Site d} :
    p ∈ sctExternalBoxPairs d n ↔ p.2 ∈ sctExteriorNeighbours d n p.1.1 := by
  classical
  constructor
  · intro hp
    rw [sctExternalBoxPairs, Finset.mem_biUnion] at hp
    obtain ⟨x, _, hp⟩ := hp
    rw [Finset.mem_image] at hp
    obtain ⟨y, hy, hyp⟩ := hp
    rw [← hyp]
    exact hy
  · intro hp
    rw [sctExternalBoxPairs, Finset.mem_biUnion]
    refine ⟨p.1, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨p.2, hp, rfl⟩


theorem sctExternalBoundaryCorr_eq_sum_vertices {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) :
    sctExternalBoundaryCorr d beta n T =
      ∑ x : sctBox d n,
        if x ∈ T then
          ((sctExteriorNeighbours d n x.1).card : ℝ) *
            corrOriginInner d beta (sctCutSites T) x.1
        else 0 := by
  classical
  let B := (boundaryEdges d (sctCutSites T)).filter (fun e => e.2 ∉ box d n)
  let P := (sctExternalBoxPairs d n).filter (fun p => p.1 ∈ T)
  let i : Site d × Site d → sctBox d n × Site d := fun e =>
    (sctBoxize d n e.1, e.2)
  have hbij :
      (∑ e ∈ B, corrOriginInner d beta (sctCutSites T) e.1) =
        ∑ p ∈ P, corrOriginInner d beta (sctCutSites T) p.1.1 := by
    apply Finset.sum_bij (fun e _ => i e)
    · intro e he
      have heB := Finset.mem_filter.mp he
      obtain ⟨_, _, h1S, h2S, _⟩ := boundaryEdges_outer heB.1
      have h1box := sctCutSites_subset_box T h1S
      have hxT : sctBoxize d n e.1 ∈ T := by
        apply mem_sctCutSites.mp
        simpa [sctBoxize_val h1box] using h1S
      rw [Finset.mem_filter]
      refine ⟨?_, hxT⟩
      rw [mem_sctExternalBoxPairs]
      rw [sctExteriorNeighbours, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      constructor
      · simpa [i, sctBoxize_val h1box] using boundaryEdges_adj heB.1
      · exact heB.2
    · intro a ha b hb hab
      have haB := (Finset.mem_filter.mp ha).1
      have hbB := (Finset.mem_filter.mp hb).1
      obtain ⟨_, _, ha1S, _, _⟩ := boundaryEdges_outer haB
      obtain ⟨_, _, hb1S, _, _⟩ := boundaryEdges_outer hbB
      have ha1box := sctCutSites_subset_box T ha1S
      have hb1box := sctCutSites_subset_box T hb1S
      apply Prod.ext
      · have hv := congrArg (fun p : sctBox d n × Site d => p.1.1) hab
        simpa [i, sctBoxize_val ha1box, sctBoxize_val hb1box] using hv
      · exact congrArg (fun p : sctBox d n × Site d => p.2) hab
    · intro p hp
      have hpP := Finset.mem_filter.mp hp
      have hpExt := mem_sctExternalBoxPairs.mp hpP.1
      have hadj : (hypercubicLattice d).Adj p.1.1 p.2 := by
        rw [sctExteriorNeighbours, Finset.mem_filter,
          SimpleGraph.mem_neighborFinset] at hpExt
        exact hpExt.1
      have hybox : p.2 ∉ box d n := by
        rw [sctExteriorNeighbours, Finset.mem_filter] at hpExt
        exact hpExt.2
      have hyS : p.2 ∉ sctCutSites T := fun hy =>
        hybox (sctCutSites_subset_box T hy)
      refine ⟨(p.1.1, p.2), ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨mem_boundaryEdges_of_adj (sctCutSites T)
          (mem_sctCutSites.mpr hpP.2) hyS hadj, hybox⟩
      · have hpboxize : sctBoxize d n p.1.1 = p.1 :=
          Subtype.ext (sctBoxize_val p.1.2)
        simp [i, hpboxize]
    · intro e he
      have heB := Finset.mem_filter.mp he
      obtain ⟨_, _, h1S, _, _⟩ := boundaryEdges_outer heB.1
      have h1box := sctCutSites_subset_box T h1S
      simp [i, sctBoxize_val h1box]
  have hpairwise : ((Finset.univ : Finset (sctBox d n)) : Set (sctBox d n)).PairwiseDisjoint
      (fun x => (sctExteriorNeighbours d n x.1).image fun y => (x, y)) := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro p hpx hpy
    rw [Finset.mem_image] at hpx hpy
    obtain ⟨_, _, rfl⟩ := hpx
    obtain ⟨_, _, hp⟩ := hpy
    exact hxy (congrArg (fun p : sctBox d n × Site d => p.1) hp).symm
  have hregroup :
      (∑ p ∈ P, corrOriginInner d beta (sctCutSites T) p.1.1) =
        ∑ x : sctBox d n,
          if x ∈ T then
            ((sctExteriorNeighbours d n x.1).card : ℝ) *
              corrOriginInner d beta (sctCutSites T) x.1
          else 0 := by
    unfold P sctExternalBoxPairs
    rw [Finset.sum_filter]
    rw [Finset.sum_biUnion hpairwise]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ T
    · rw [if_pos hx]
      rw [Finset.sum_image]
      · simp [hx]
      · intro a _ b _ hab
        exact congrArg (fun p : sctBox d n × Site d => p.2) hab
    · rw [if_neg hx]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨y, _, rfl⟩ := hp
      simp [hx]
  unfold sctExternalBoundaryCorr
  change (∑ e ∈ B, corrOriginInner d beta (sctCutSites T) e.1) = _
  rw [hbij, hregroup]


theorem sct_sum_cutCorr_eq_covariance {d n : ℕ} (beta h : ℝ)
    (x : sctBox d n) (hox : sctBoxOrigin d n ≠ x) :
    (∑ T : Finset (sctBox d n),
      if sctBoxOrigin d n ∈ T ∧ x ∈ T then
        corrOriginInner d beta (sctCutSites T) x.1 *
          sctCurrentCutMass d beta h n T
      else 0) =
      sctBoxCovariance d beta h n x := by
  have hc := sum_localCorr_baseCutMass_eq_fieldCovariance
    (sctBoxGraph d n) beta h hox
  have hlhs :
      (∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T ∧ x ∈ T then
          expectationJ (sctBoxGraph d n) beta
              (couplingIn (fun _ => 1) T) {sctBoxOrigin d n, x} *
            sctCurrentCutMass d beta h n T
        else 0) =
      ∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T ∧ x ∈ T then
          corrOriginInner d beta (sctCutSites T) x.1 *
            sctCurrentCutMass d beta h n T
        else 0 := by
    apply Finset.sum_congr rfl
    intro T _
    by_cases ho : sctBoxOrigin d n ∈ T <;> by_cases hx : x ∈ T
    · rw [if_pos ⟨ho, hx⟩, if_pos ⟨ho, hx⟩,
        sct_localCorr_eq_corrOriginInner beta T ho hx hox]
    · simp [ho, hx]
    · simp [ho, hx]
    · simp [ho, hx]
  rw [← hlhs]
  unfold sctCurrentCutMass
  rw [hc]
  unfold sctBoxCovariance sctOriginMag sctBoxMag
  have hpair : spinProd ({sctBoxOrigin d n, x} : Finset (sctBox d n)) =
      (fun s => spin s (sctBoxOrigin d n) * spin s x) := by
    funext s
    rw [spinProd, Finset.prod_pair hox]
  have hoSpin : spinProd ({sctBoxOrigin d n} : Finset (sctBox d n)) =
      (fun s => spin s (sctBoxOrigin d n)) := by funext s; simp [spinProd]
  have hxSpin : spinProd ({x} : Finset (sctBox d n)) =
      (fun s => spin s x) := by funext s; simp [spinProd]
  rw [hpair, hoSpin, hxSpin]


theorem sctCurrentBoundaryError_eq_boundaryCovarianceError
    {d n : ℕ} (beta h : ℝ) (hn : 1 ≤ n) :
    sctCurrentBoundaryError d beta h n =
      sctBoundaryCovarianceError d beta h n := by
  unfold sctCurrentBoundaryError
  simp_rw [sctExternalBoundaryCorr_eq_sum_vertices beta]
  have hexpand :
      (∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T then
          (∑ x : sctBox d n,
            if x ∈ T then
              ((sctExteriorNeighbours d n x.1).card : ℝ) *
                corrOriginInner d beta (sctCutSites T) x.1
            else 0) * sctCurrentCutMass d beta h n T
        else 0) =
      ∑ T : Finset (sctBox d n), ∑ x : sctBox d n,
        if sctBoxOrigin d n ∈ T ∧ x ∈ T then
          ((sctExteriorNeighbours d n x.1).card : ℝ) *
            (corrOriginInner d beta (sctCutSites T) x.1 *
              sctCurrentCutMass d beta h n T)
        else 0 := by
    apply Finset.sum_congr rfl
    intro T _
    by_cases ho : sctBoxOrigin d n ∈ T
    · rw [if_pos ho, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ T <;> simp [ho, hx] <;> ring
    · rw [if_neg ho]
      symm
      apply Finset.sum_eq_zero
      intro x _
      simp [ho]
  rw [hexpand, Finset.sum_comm]
  unfold sctBoundaryCovarianceError
  apply Finset.sum_congr rfl
  intro x _
  by_cases hox : sctBoxOrigin d n = x
  · subst x
    have horigin : (sctBoxOrigin d n).1 ∈ box d (n - 1) := by
      intro i
      simp [sctBoxOrigin]
    rw [sctExteriorNeighbours_eq_empty_of_mem_pred hn horigin]
    simp
  · calc
      (∑ T : Finset (sctBox d n),
        if sctBoxOrigin d n ∈ T ∧ x ∈ T then
          ((sctExteriorNeighbours d n x.1).card : ℝ) *
            (corrOriginInner d beta (sctCutSites T) x.1 *
              sctCurrentCutMass d beta h n T)
        else 0) =
          ((sctExteriorNeighbours d n x.1).card : ℝ) *
            ∑ T : Finset (sctBox d n),
              if sctBoxOrigin d n ∈ T ∧ x ∈ T then
                corrOriginInner d beta (sctCutSites T) x.1 *
                  sctCurrentCutMass d beta h n T
              else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        by_cases ho : sctBoxOrigin d n ∈ T <;> by_cases hx : x ∈ T <;>
          simp [ho, hx] <;> ring
      _ = ((sctExteriorNeighbours d n x.1).card : ℝ) *
          sctBoxCovariance d beta h n x := by
        rw [sct_sum_cutCorr_eq_covariance beta h x hox]


theorem sct_finite_meanfield_inequality_concrete {d n : ℕ}
    (beta h infphi : ℝ) (hn : 1 ≤ n)
    (hbeta : 0 < beta) (hh : 0 < h)
    (hinf : ∀ S : Finset (Site d), origin d ∈ S →
      infphi ≤ phiIsing d beta S) :
    deriv (fun b => (sctOriginMag d b h n) ^ 2) beta ≥
      2 * sctLatticeC d beta h n *
        ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          sctBoundaryCovarianceError d beta h n) := by
  rw [← sctCurrentBoundaryError_eq_boundaryCovarianceError beta h hn]
  exact sct_finite_meanfield_inequality beta h infphi hbeta hh hinf

end Sharpness
end StatMech
