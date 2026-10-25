/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part4


namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

theorem hexStrip_singleRegion_returningSAW_eq_nil
    (a : ℂ) (h0 : ℤ) :
    ∀ ts : List ℤ,
      (ofTurns a h0 ts).IsLegalSAW
        ∧ (ofTurns a h0 ts).StaysIn (hexStrip_singleRegion a).inRegion
        ∧ (ofTurns a h0 ts).EndsAt a → ts = [] :=
  (hexStrip_singleRegion a).returningSAW_eq_nil_of_directedStartIncidence h0
    (hexStrip_singleRegion_directedStartIncidence a h0)


theorem hexStrip_singleRegion_directedStartIncidence_nonempty
    (a : ℂ) (h0 : ℤ) :
    Nonempty ((hexStrip_singleRegion a).DirectedStartIncidence h0) :=
  ⟨hexStrip_singleRegion_directedStartIncidence a h0⟩


theorem returningSAW_eq_nil_of_startInteriorUnique
    (R : HexFiniteRegion) (h0 : ℤ) (hstart : R.StartInteriorUnique h0) :
    ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
  intro ts hts
  have hlastMemWalk := hexInfra_verticesAux_getLast_mem R.start h0 ts
  have hlastMemVerts :
      hexInfra_midAccum R.start h0 ts
          + halfStep (hexInfra_headAccum h0 ts) ∈ R.verts :=
    R.vertices_mem R.start h0 ts hts.2.1 _ hlastMemWalk
  have hend : hexInfra_midAccum R.start h0 ts = R.start := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact hts.2.2
  have hlast : hexInfra_midAccum R.start h0 ts
      + halfStep (hexInfra_headAccum h0 ts) = R.start + halfStep h0 := by
    rw [hend] at hlastMemVerts
    rw [hend]
    exact hstart _ hlastMemVerts
  exact hexLegalSAW_eq_nil_of_lastVertex_eq_first
    R.start h0 ts hts.1 hlast


theorem returningSAW_eq_nil
    (R : HexFiniteRegion) (h0 : ℤ) :
    ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = [] := by
  intro ts hts
  exact hexReturningLegalSAW_eq_nil R.start h0 ts hts.1 hts.2.2

end HexFiniteRegion


theorem parafObservable_start_eq_weight_of_unique
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (sigma x : ℝ)
    (hreg : inRegion a)
    (hunique : ∀ ts : List ℤ,
      (ofTurns a h0 ts).IsLegalSAW
        ∧ (ofTurns a h0 ts).StaysIn inRegion
        ∧ (ofTurns a h0 ts).EndsAt a → ts = []) :
    parafObservable inRegion a h0 a sigma x = (x : ℂ) := by
  unfold parafObservable
  calc
    (∑' ts : List ℤ, parafSummand inRegion a h0 a sigma x ts)
        = parafSummand inRegion a h0 a sigma x [] := by
          apply tsum_eq_single
          intro ts hts
          by_cases hguard :
              (ofTurns a h0 ts).IsLegalSAW
                ∧ (ofTurns a h0 ts).StaysIn inRegion
                ∧ (ofTurns a h0 ts).EndsAt a
          · exact (hts (hunique ts hguard)).elim
          · unfold parafSummand
            rw [if_neg hguard]
    _ = (x : ℂ) := parafSummand_self inRegion a h0 sigma x hreg


theorem parafObservable_start_eq_weight
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (sigma x : ℝ)
    (hreg : inRegion a) :
    parafObservable inRegion a h0 a sigma x = (x : ℂ) :=
  parafObservable_start_eq_weight_of_unique inRegion a h0 sigma x hreg
    (fun ts hts => hexReturningLegalSAW_eq_nil a h0 ts hts.1 hts.2.2)

namespace HexFObsBoundaryData

variable (B : HexFObsBoundaryData)


theorem boundaryIdentity_fa :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = B.Fa := by
  have hraw := B.raw
  rw [B.alphaRest_eq, B.betaSum_eq, B.epsSum_eq, B.epsbarSum_eq] at hraw
  have hap := hbi_alphaPhase
  have hsp := hbi_slantPhase
  have hreal :
      (-((B.Fa : ℝ) + (-(hexBdryCl) * B.lam))
          + B.ups + hexBdryCt * B.tau : ℝ) = 0 := by
    have hcast :
        ((-((B.Fa : ℝ) + (-(hexBdryCl) * B.lam))
            + B.ups + hexBdryCt * B.tau : ℝ) : ℂ) = 0 := by
      push_cast
      push_cast at hraw hap hsp
      linear_combination hraw + (B.lam : ℂ) * hap - (B.tau : ℂ) * hsp
    exact_mod_cast hcast
  linarith

end HexFObsBoundaryData

variable {V : Type*} [DecidableEq V]

namespace HexFiniteStripBoundaryData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} (B : HexFiniteStripBoundaryData R h0 D P)


theorem boundary_identity_fa :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = B.Fa :=
  B.toFObsBoundaryData.boundaryIdentity_fa


theorem normalized_boundary_identity (hFa : B.Fa = hexChi) :
    hexBdryCl * (hexChi⁻¹ * B.lam)
      + hexBdryCt * (hexChi⁻¹ * B.tau)
      + hexChi⁻¹ * B.ups = 1 := by
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have h := B.boundary_identity_fa
  rw [hFa] at h
  calc
    hexBdryCl * (hexChi⁻¹ * B.lam)
          + hexBdryCt * (hexChi⁻¹ * B.tau)
          + hexChi⁻¹ * B.ups
        = hexChi⁻¹ *
            (hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups) := by ring
    _ = hexChi⁻¹ * hexChi := by rw [h]
    _ = 1 := inv_mul_cancel₀ hchi


theorem normalized_contour_boundary_identity (hFa : B.Fa = hexChi) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 := by
  rw [← B.lam_eq, ← B.tau_eq, ← B.ups_eq]
  exact B.normalized_boundary_identity hFa


theorem Fa_eq_hexChi_of_unique_start
    (hreg : R.inRegion R.start)
    (hunique : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = []) :
    B.Fa = hexChi := by
  apply Complex.ofReal_injective
  calc
    (B.Fa : ℂ) = D.obs R.start := B.Fa_eq
    _ = parafObservable R.inRegion R.start h0 R.start (5 / 8) hexChi :=
      B.obs_eq R.start
    _ = (hexChi : ℂ) :=
      parafObservable_start_eq_weight_of_unique
        R.inRegion R.start h0 (5 / 8) hexChi hreg hunique


theorem Fa_eq_hexChi : B.Fa = hexChi := by
  apply B.Fa_eq_hexChi_of_unique_start
  · simpa [HexFiniteRegion.inRegion] using R.start_mem
  · exact R.returningSAW_eq_nil h0


theorem normalized_boundary_identity_closed :
    hexBdryCl * (hexChi⁻¹ * B.lam)
      + hexBdryCt * (hexChi⁻¹ * B.tau)
      + hexChi⁻¹ * B.ups = 1 :=
  B.normalized_boundary_identity B.Fa_eq_hexChi


theorem normalized_contour_boundary_identity_closed :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity B.Fa_eq_hexChi


theorem normalized_contour_boundary_identity_of_unique_start
    (hreg : R.inRegion R.start)
    (hunique : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = []) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity
    (B.Fa_eq_hexChi_of_unique_start hreg hunique)


theorem Fa_eq_hexChi_of_directedStartIncidence
    (S : R.DirectedStartIncidence h0) : B.Fa = hexChi := by
  apply B.Fa_eq_hexChi_of_unique_start
  · simpa [HexFiniteRegion.inRegion] using R.start_mem
  · exact R.returningSAW_eq_nil_of_directedStartIncidence h0 S


theorem normalized_contour_boundary_identity_of_directedStartIncidence
    (S : R.DirectedStartIncidence h0) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity
    (B.Fa_eq_hexChi_of_directedStartIncidence S)


theorem Fa_eq_hexChi_of_straightStart_reverse
    (interior : ℂ → Prop)
    (S : HexStraightSide R.inRegion interior R.start h0 R.start)
    (hreverse : halfStep S.H = -halfStep h0) : B.Fa = hexChi :=
  B.Fa_eq_hexChi_of_directedStartIncidence
    (R.directedStartIncidence_of_straightStart_reverse
      h0 interior S hreverse)


theorem normalized_contour_boundary_identity_of_straightStart_reverse
    (interior : ℂ → Prop)
    (S : HexStraightSide R.inRegion interior R.start h0 R.start)
    (hreverse : halfStep S.H = -halfStep h0) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity_of_directedStartIncidence
    (R.directedStartIncidence_of_straightStart_reverse
      h0 interior S hreverse)


theorem Fa_eq_hexChi_of_stripStartGeometry
    (dregion : ℂ → ℤ → Prop)
    (huniq : ∀ h : ℤ,
      hexStripInterior dregion (R.start + halfStep h) →
        halfStep h = halfStep h0)
    (hbridge : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start →
      hexStripStaysInDir dregion R.start h0 ts) :
    B.Fa = hexChi :=
  B.Fa_eq_hexChi_of_directedStartIncidence
    (R.directedStartIncidence_of_stripStartGeometry
      h0 dregion huniq hbridge)


theorem normalized_contour_boundary_identity_of_stripStartGeometry
    (dregion : ℂ → ℤ → Prop)
    (huniq : ∀ h : ℤ,
      hexStripInterior dregion (R.start + halfStep h) →
        halfStep h = halfStep h0)
    (hbridge : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).IsLegalSAW
        ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion
        ∧ (ofTurns R.start h0 ts).EndsAt R.start →
      hexStripStaysInDir dregion R.start h0 ts) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity_of_directedStartIncidence
    (R.directedStartIncidence_of_stripStartGeometry
      h0 dregion huniq hbridge)


theorem Fa_eq_hexChi_singleRegion
    {a : ℂ}
    (B₁ : HexFiniteStripBoundaryData (hexStrip_singleRegion a) h0 D P) :
    B₁.Fa = hexChi :=
  B₁.Fa_eq_hexChi_of_directedStartIncidence
    (HexFiniteRegion.hexStrip_singleRegion_directedStartIncidence a h0)


theorem normalized_contour_boundary_identity_singleRegion
    {a : ℂ}
    (B₁ : HexFiniteStripBoundaryData (hexStrip_singleRegion a) h0 D P) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda (hexStrip_singleRegion a).inRegion
          a h0 B₁.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus (hexStrip_singleRegion a).inRegion
              a h0 B₁.sides hexChi
            + hexContourTauMinus (hexStrip_singleRegion a).inRegion
              a h0 B₁.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon (hexStrip_singleRegion a).inRegion
            a h0 B₁.sides hexChi = 1 :=
  B₁.normalized_contour_boundary_identity_of_directedStartIncidence
    (HexFiniteRegion.hexStrip_singleRegion_directedStartIncidence a h0)


theorem Fa_eq_hexChi_of_startInteriorUnique
    (hstart : R.StartInteriorUnique h0) : B.Fa = hexChi := by
  apply B.Fa_eq_hexChi_of_unique_start
  · simpa [HexFiniteRegion.inRegion] using R.start_mem
  · exact R.returningSAW_eq_nil_of_startInteriorUnique h0 hstart


theorem normalized_contour_boundary_identity_of_startInteriorUnique
    (hstart : R.StartInteriorUnique h0) :
    hexBdryCl *
        (hexChi⁻¹ * hexContourLambda R.inRegion R.start h0 B.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 B.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 B.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 B.sides hexChi = 1 :=
  B.normalized_contour_boundary_identity
    (B.Fa_eq_hexChi_of_startInteriorUnique hstart)

end HexFiniteStripBoundaryData
end StatMech.Universality
