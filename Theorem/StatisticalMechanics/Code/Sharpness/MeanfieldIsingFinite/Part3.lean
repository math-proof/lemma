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
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part3
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


theorem sct_normalizedDeltaLowerMass_eq_orientedCutMass
    {d n : ℕ} (beta h : ℝ) {x y : sctBox d n}
    (hox : sctBoxOrigin d n ≠ x) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      isingDeltaLowerMass (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1))
        (some (sctBoxOrigin d n)) (some x) (some y) none =
      sctOrientedCutMass d beta h n x y := by
  rw [normalizedDeltaLowerMass_fieldGhost (sctBoxGraph d n) beta h hox]
  unfold sctOrientedCutMass sctCurrentCutMass
  apply Finset.sum_congr rfl
  intro T _
  by_cases ho : sctBoxOrigin d n ∈ T <;> by_cases hx : x ∈ T <;>
    by_cases hy : y ∉ T
  · rw [if_pos ⟨ho, hx, hy⟩, if_pos ⟨ho, hx, hy⟩,
      sct_localCorr_eq_corrOriginInner beta T ho hx hox]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]
  · simp [ho, hx, hy]


theorem sct_normalizedDeltaSelfLowerMass_eq_orientedCutMass
    {d n : ℕ} (beta h : ℝ) (y : sctBox d n) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      isingDeltaSelfLowerMass (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1))
        (some (sctBoxOrigin d n)) (some y) none =
      sctOrientedCutMass d beta h n (sctBoxOrigin d n) y := by
  rw [normalizedDeltaSelfLowerMass_fieldGhost
    (sctBoxGraph d n) beta h (sctBoxOrigin d n) y]
  unfold sctOrientedCutMass sctCurrentCutMass
  apply Finset.sum_congr rfl
  intro T _
  by_cases ho : sctBoxOrigin d n ∈ T <;> by_cases hy : y ∉ T
  · simp only [ho, hy, not_false_eq_true, and_self, and_true, if_true]
    have hc : corrOriginInner d beta (sctCutSites T) (sctBoxOrigin d n).1 = 1 := by
      simpa using sct_corrOriginInner_origin beta T ho
    rw [hc, one_mul]
  · simp [ho, hy]
  · simp [ho, hy]
  · simp [ho, hy]


theorem sctLatticeC_le_siteRatio {d n : ℕ} (beta h : ℝ)
    (y : sctBox d n) :
    sctLatticeC d beta h n ≤
      sctOriginMag d beta h n / sctBoxMag d beta h n y := by
  unfold sctLatticeC sct_cInfDep sctBoxSites
  exact Finset.inf'_le _ (Finset.mem_univ y)


theorem sctLatticeC_nonneg {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) :
    0 ≤ sctLatticeC d beta h n := by
  unfold sctLatticeC sct_cInfDep sctBoxSites
  apply Finset.le_inf' (sctBoxSites_nonempty d n)
  intro y _
  exact div_nonneg (sctOriginMag_pos d beta h hbeta hh n).le
    (sctBoxMag_pos d beta h hbeta hh n y).le


theorem sctLatticeC_mul_siteMag_le_origin {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) (y : sctBox d n) :
    sctLatticeC d beta h n * sctBoxMag d beta h n y ≤
      sctOriginMag d beta h n := by
  have hr := sctLatticeC_le_siteRatio beta h y
  have hy := sctBoxMag_pos d beta h hbeta hh n y
  rwa [le_div_iff₀ hy] at hr


theorem sct_nonincidentBondDelta_bound {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) {x y : sctBox d n}
    (hox : sctBoxOrigin d n ≠ x) (hoy : sctBoxOrigin d n ≠ y)
    (hxy : x ≠ y) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      (sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
          (sctBoxOrigin d n) s(x, y)) ≥
      sctLatticeC d beta h n *
        (sctOrientedCutMass d beta h n x y +
          sctOrientedCutMass d beta h n y x) := by
  let K := sctBoxGraph d n
  let o := sctBoxOrigin d n
  let Jg : Sym2 (Option (sctBox d n)) → ℝ :=
    ghostCoupling h beta (fun _ => 1)
  let Zinv := (currentSum (withGhost K) beta Jg ∅)⁻¹ ^ 2
  let dxy := isingDeltaPairSum (withGhost K) beta Jg
    (some o) (some x) (some y) none
  let dyx := isingDeltaPairSum (withGhost K) beta Jg
    (some o) (some y) (some x) none
  let Lxy := isingDeltaLowerMass (withGhost K) beta Jg
    (some o) (some x) (some y) none
  let Lyx := isingDeltaLowerMass (withGhost K) beta Jg
    (some o) (some y) (some x) none
  have hJg : ∀ e : Sym2 (Option (sctBox d n)), 0 ≤ Jg e := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => cases a <;> cases b <;> simp [Jg, ghostCoupling, hh.le]
  have hdxy : 0 ≤ dxy :=
    isingDeltaPairSum_nonneg (withGhost K) beta Jg hbeta.le hJg _ _ _ _
  have hdyx : 0 ≤ dyx :=
    isingDeltaPairSum_nonneg (withGhost K) beta Jg hbeta.le hJg _ _ _ _
  have hbxy : Lxy ≤ sctBoxMag d beta h n y * dxy := by
    have hb := isingDeltaPair_field_bound K beta h hbeta.le hh.le hox hoy hxy
    have hspin : spinProd ({y} : Finset (sctBox d n)) =
        (fun s => spin s y) := by funext s; simp [spinProd]
    rw [hspin] at hb
    simpa [K, o, Jg, dxy, Lxy, sctBoxMag] using hb
  have hbyx : Lyx ≤ sctBoxMag d beta h n x * dyx := by
    have hb := isingDeltaPair_field_bound K beta h hbeta.le hh.le hoy hox hxy.symm
    have hspin : spinProd ({x} : Finset (sctBox d n)) =
        (fun s => spin s x) := by funext s; simp [spinProd]
    rw [hspin] at hb
    simpa [K, o, Jg, dyx, Lyx, sctBoxMag] using hb
  have hc : 0 ≤ sctLatticeC d beta h n :=
    sctLatticeC_nonneg beta h hbeta hh
  have hcx := sctLatticeC_mul_siteMag_le_origin beta h hbeta hh x
  have hcy := sctLatticeC_mul_siteMag_le_origin beta h hbeta hh y
  have hxy' : sctLatticeC d beta h n * Lxy ≤
      sctOriginMag d beta h n * dxy := by
    calc
      sctLatticeC d beta h n * Lxy ≤
          sctLatticeC d beta h n *
            (sctBoxMag d beta h n y * dxy) :=
        mul_le_mul_of_nonneg_left hbxy hc
      _ = (sctLatticeC d beta h n * sctBoxMag d beta h n y) * dxy := by ring
      _ ≤ sctOriginMag d beta h n * dxy :=
        mul_le_mul_of_nonneg_right hcy hdxy
  have hyx' : sctLatticeC d beta h n * Lyx ≤
      sctOriginMag d beta h n * dyx := by
    calc
      sctLatticeC d beta h n * Lyx ≤
          sctLatticeC d beta h n *
            (sctBoxMag d beta h n x * dyx) :=
        mul_le_mul_of_nonneg_left hbyx hc
      _ = (sctLatticeC d beta h n * sctBoxMag d beta h n x) * dyx := by ring
      _ ≤ sctOriginMag d beta h n * dyx :=
        mul_le_mul_of_nonneg_right hcx hdyx
  have hsplit := hcaBondDelta_nonincident_eq_deltaPair_add K beta h hox hoy hxy
  have hsum : sctLatticeC d beta h n * (Lxy + Lyx) ≤
      sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta K beta h o s(x, y) := by
    rw [hsplit]
    calc
      sctLatticeC d beta h n * (Lxy + Lyx) =
          sctLatticeC d beta h n * Lxy +
            sctLatticeC d beta h n * Lyx := by ring
      _ ≤ sctOriginMag d beta h n * dxy +
          sctOriginMag d beta h n * dyx := add_le_add hxy' hyx'
      _ = sctOriginMag d beta h n * (dxy + dyx) := by ring
  have hZ : 0 ≤ Zinv := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hsum hZ
  have hcutxy := sct_normalizedDeltaLowerMass_eq_orientedCutMass
    beta h (x := x) (y := y) hox
  have hcutyx := sct_normalizedDeltaLowerMass_eq_orientedCutMass
    beta h (x := y) (y := x) hoy
  change Zinv * (sctOriginMag d beta h n *
      HcovAssembly.hcaBondDelta K beta h o s(x, y)) ≥ _
  calc
    sctLatticeC d beta h n *
        (sctOrientedCutMass d beta h n x y +
          sctOrientedCutMass d beta h n y x) =
        Zinv * (sctLatticeC d beta h n * (Lxy + Lyx)) := by
      rw [← hcutxy, ← hcutyx]
      dsimp [Zinv, Lxy, Lyx, K, Jg, o]
      ring
    _ ≤ Zinv * (sctOriginMag d beta h n *
          HcovAssembly.hcaBondDelta K beta h o s(x, y)) := hscaled


theorem sct_incidentBondDelta_bound {d n : ℕ} (beta h : ℝ)
    (hbeta : 0 < beta) (hh : 0 < h) (y : sctBox d n)
    (hoy : sctBoxOrigin d n ≠ y) :
    (currentSum (withGhost (sctBoxGraph d n)) beta
        (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 *
      (sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h
          (sctBoxOrigin d n) s(sctBoxOrigin d n, y)) ≥
      sctLatticeC d beta h n *
        sctOrientedCutMass d beta h n (sctBoxOrigin d n) y := by
  let K := sctBoxGraph d n
  let o := sctBoxOrigin d n
  let Jg : Sym2 (Option (sctBox d n)) → ℝ :=
    ghostCoupling h beta (fun _ => 1)
  let Zinv := (currentSum (withGhost K) beta Jg ∅)⁻¹ ^ 2
  let L := isingDeltaSelfLowerMass (withGhost K) beta Jg (some o) (some y) none
  have hb : L ≤ sctBoxMag d beta h n y *
      HcovAssembly.hcaBondDelta K beta h o s(o, y) := by
    have hb' := hcaBondDelta_incident_bound K beta h hbeta.le hh.le o y hoy
    have hspin : spinProd ({y} : Finset (sctBox d n)) =
        (fun s => spin s y) := by funext s; simp [spinProd]
    rw [hspin] at hb'
    simpa [K, o, Jg, L, sctBoxMag] using hb'
  have hc : 0 ≤ sctLatticeC d beta h n :=
    sctLatticeC_nonneg beta h hbeta hh
  have hcy := sctLatticeC_mul_siteMag_le_origin beta h hbeta hh y
  have hd : 0 ≤ HcovAssembly.hcaBondDelta K beta h o s(o, y) :=
    HcovAssembly.hcaBondDelta_nonneg K beta h hbeta.le hh.le o s(o, y)
  have hraw : sctLatticeC d beta h n * L ≤
      sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta K beta h o s(o, y) := by
    calc
      sctLatticeC d beta h n * L ≤
          sctLatticeC d beta h n *
            (sctBoxMag d beta h n y *
              HcovAssembly.hcaBondDelta K beta h o s(o, y)) :=
        mul_le_mul_of_nonneg_left hb hc
      _ = (sctLatticeC d beta h n * sctBoxMag d beta h n y) *
          HcovAssembly.hcaBondDelta K beta h o s(o, y) := by ring
      _ ≤ sctOriginMag d beta h n *
          HcovAssembly.hcaBondDelta K beta h o s(o, y) :=
        mul_le_mul_of_nonneg_right hcy hd
  have hscaled := mul_le_mul_of_nonneg_left hraw (sq_nonneg _ : 0 ≤ Zinv)
  have hcut := sct_normalizedDeltaSelfLowerMass_eq_orientedCutMass beta h y
  change Zinv * (sctOriginMag d beta h n *
      HcovAssembly.hcaBondDelta K beta h o s(o, y)) ≥ _
  calc
    sctLatticeC d beta h n *
        sctOrientedCutMass d beta h n o y =
      Zinv * (sctLatticeC d beta h n * L) := by
        rw [← hcut]
        dsimp [Zinv, L, K, Jg, o]
        ring
    _ ≤ Zinv * (sctOriginMag d beta h n *
        HcovAssembly.hcaBondDelta K beta h o s(o, y)) := hscaled


end Sharpness
end StatMech
