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
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part9
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


theorem sct_internalBoundaryMass_lower {d n : ℕ} (beta h infphi : ℝ)
    (hbeta : 0 < beta) (hh : 0 ≤ h)
    (hinf : ∀ S : Finset (Site d), origin d ∈ S → infphi ≤ phiIsing d beta S) :
    (∑ T : Finset (sctBox d n),
      if sctBoxOrigin d n ∈ T then
        sctInternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
      else 0) ≥
      (1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
        sctCurrentBoundaryError d beta h n := by
  have hJ : ∀ e : Sym2 (Option (sctBox d n)),
      0 ≤ ghostCoupling h beta (fun _ => 1) e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => cases a <;> cases b <;> simp [ghostCoupling, hh]
  have hmass (T : Finset (sctBox d n)) : 0 ≤ sctCurrentCutMass d beta h n T :=
    isingCutMass_nonneg (withGhost (sctBoxGraph d n)) beta
      (ghostCoupling h beta (fun _ => 1)) hbeta.le hJ none (T.map someEmb)
  let full : Finset (sctBox d n) → ℝ := fun T =>
    ∑ e ∈ boundaryEdges d (sctCutSites T),
      corrOriginInner d beta (sctCutSites T) e.1
  have hfull (T : Finset (sctBox d n)) (ho : sctBoxOrigin d n ∈ T) :
      (1 / beta) * infphi ≤ full T := by
    have hoS : origin d ∈ sctCutSites T := by
      exact Finset.mem_image.mpr ⟨sctBoxOrigin d n, ho, rfl⟩
    have hi := hinf (sctCutSites T) hoS
    have hphi : phiIsing d beta (sctCutSites T) = Real.tanh beta * full T := rfl
    have hcorr : 0 ≤ full T := by
      apply Finset.sum_nonneg
      intro e _
      exact corrOriginInner_nonneg d hbeta.le (sctCutSites T) e.1
    have htanh := tanh_le_self_of_nonneg hbeta.le
    have hupper : phiIsing d beta (sctCutSites T) ≤ beta * full T := by
      rw [hphi]
      exact mul_le_mul_of_nonneg_right htanh hcorr
    have : infphi ≤ beta * full T := hi.trans hupper
    calc
      (1 / beta) * infphi = infphi / beta := by ring
      _ ≤ full T := (div_le_iff₀ hbeta).2 (by simpa [mul_comm] using this)
  have hweighted :
      (1 / beta) * infphi *
          (∑ T : Finset (sctBox d n),
            if sctBoxOrigin d n ∈ T then sctCurrentCutMass d beta h n T else 0) ≤
        ∑ T : Finset (sctBox d n),
          if sctBoxOrigin d n ∈ T then full T * sctCurrentCutMass d beta h n T
          else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro T _
    by_cases ho : sctBoxOrigin d n ∈ T
    · rw [if_pos ho, if_pos ho]
      exact mul_le_mul_of_nonneg_right (hfull T ho) (hmass T)
    · simp [ho]
  rw [sct_sum_currentCutMass] at hweighted
  unfold sctCurrentBoundaryError
  calc
    (1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          (∑ T : Finset (sctBox d n),
            if sctBoxOrigin d n ∈ T then
              sctExternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
            else 0) =
        ((1 / beta) * infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          (∑ T : Finset (sctBox d n),
            if sctBoxOrigin d n ∈ T then
              sctExternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
            else 0) := by ring
    _ ≤ (∑ T : Finset (sctBox d n),
          if sctBoxOrigin d n ∈ T then full T * sctCurrentCutMass d beta h n T
          else 0) -
        (∑ T : Finset (sctBox d n),
          if sctBoxOrigin d n ∈ T then
            sctExternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
          else 0) := sub_le_sub_right hweighted _
    _ = ∑ T : Finset (sctBox d n),
          if sctBoxOrigin d n ∈ T then
            sctInternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T
          else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro T _
      by_cases ho : sctBoxOrigin d n ∈ T
      · rw [if_pos ho, if_pos ho, if_pos ho]
        dsimp [full]
        rw [sct_boundaryCorr_split beta T]
        ring
      · simp [ho]


theorem sct_finite_meanfield_inequality {d n : ℕ} (beta h infphi : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h)
    (hinf : ∀ S : Finset (Site d), origin d ∈ S → infphi ≤ phiIsing d beta S) :
    deriv (fun b => (sctOriginMag d b h n) ^ 2) beta ≥
      2 * sctLatticeC d beta h n *
        ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          sctCurrentBoundaryError d beta h n) := by
  let K := sctBoxGraph d n
  let o := sctBoxOrigin d n
  let Jg : Sym2 (Option (sctBox d n)) → ℝ :=
    ghostCoupling h beta (fun _ => 1)
  let Zinv := (currentSum (withGhost K) beta Jg ∅)⁻¹ ^ 2
  let bondSum := ∑ e ∈ K.edgeFinset,
    HcovAssembly.hcaBondDelta K beta h o e
  let fieldSum := ∑ z,
    HcovAssembly.hcaFieldDelta K beta h o z
  have hd := HcovAssembly.hca_deriv_magnetization_eq_currentDelta K beta h o
  change HasDerivAt (fun b => sctOriginMag d b h n)
    ((1 / (currentSum (withGhost K) beta Jg ∅) ^ 2) *
      (bondSum + h * fieldSum)) beta at hd
  have hd2 := hd.pow 2
  have hderiv : deriv (fun b => (sctOriginMag d b h n) ^ 2) beta =
      2 * sctOriginMag d beta h n * Zinv * (bondSum + h * fieldSum) := by
    change deriv ((fun b => sctOriginMag d b h n) ^ 2) beta = _
    rw [hd2.deriv]
    dsimp [Zinv]
    have hZ : currentSum (withGhost K) beta Jg ∅ ≠ 0 :=
      ne_of_gt (Ising.acr_currentSum_empty_pos (withGhost K) beta Jg)
    field_simp
  have hfield : 0 ≤ fieldSum := by
    unfold fieldSum
    apply Finset.sum_nonneg
    intro z _
    exact HcovAssembly.hcaFieldDelta_nonneg K beta h hbeta.le hh.le o z
  have hm : 0 ≤ sctOriginMag d beta h n :=
    (sctOriginMag_pos d beta h hbeta hh n).le
  have hZinv : 0 ≤ Zinv := sq_nonneg _
  have hdrop :
      2 * sctOriginMag d beta h n * Zinv * bondSum ≤
        2 * sctOriginMag d beta h n * Zinv * (bondSum + h * fieldSum) := by
    have hext : 0 ≤ h * fieldSum := mul_nonneg hh.le hfield
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hext)
      (mul_nonneg (mul_nonneg (by norm_num) hm) hZinv)
  have hbond := sct_sum_bondDelta_bound (d := d) (n := n) beta h hbeta hh
  have hedge :
      sctLatticeC d beta h n *
          (∑ e ∈ K.edgeFinset, sctEdgeCutMass d beta h n e) ≤
        Zinv * (sctOriginMag d beta h n * bondSum) := by
    simpa [K, o, Jg, Zinv, bondSum] using hbond
  have hreassemble := sct_sum_edgeCutMass_eq_sum_internalBoundary
    (d := d) (n := n) beta h
  have hmain := sct_internalBoundaryMass_lower
    (d := d) (n := n) beta h infphi hbeta hh.le hinf
  have hc : 0 ≤ sctLatticeC d beta h n :=
    sctLatticeC_nonneg beta h hbeta hh
  have hmainc := mul_le_mul_of_nonneg_left hmain hc
  rw [← hreassemble] at hmainc
  rw [hderiv]
  calc
    2 * sctLatticeC d beta h n *
        ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          sctCurrentBoundaryError d beta h n) =
      2 * (sctLatticeC d beta h n *
        ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) -
          sctCurrentBoundaryError d beta h n)) := by ring
    _ ≤ 2 * (sctLatticeC d beta h n *
        ∑ e ∈ K.edgeFinset, sctEdgeCutMass d beta h n e) :=
      mul_le_mul_of_nonneg_left hmainc (by norm_num)
    _ ≤ 2 * (Zinv * (sctOriginMag d beta h n * bondSum)) :=
      mul_le_mul_of_nonneg_left hedge (by norm_num)
    _ = 2 * sctOriginMag d beta h n * Zinv * bondSum := by ring
    _ ≤ 2 * sctOriginMag d beta h n * Zinv * (bondSum + h * fieldSum) := hdrop


end Sharpness
end StatMech
