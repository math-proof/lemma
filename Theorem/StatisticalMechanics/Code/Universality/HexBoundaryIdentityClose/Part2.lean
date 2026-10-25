/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConnFinal
import Structure.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose


namespace StatMech.Universality

open Complex Filter Topology

open scoped Real BigOperators Topology


namespace HexFObsBoundaryData

variable (B : HexFObsBoundaryData)


theorem boundaryIdentity (hFa : B.Fa = 1) :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = 1 := by
  have hraw := B.raw
  
  rw [B.alphaRest_eq, B.betaSum_eq, B.epsSum_eq, B.epsbarSum_eq] at hraw
  
  have hap := hbi_alphaPhase          
  have hsp := hbi_slantPhase          
  
  
  
  have hreal : (-((B.Fa : ℝ) + (-(hexBdryCl) * B.lam)) + B.ups + hexBdryCt * B.tau : ℝ) = 0 := by
    have hcast : ((-((B.Fa : ℝ) + (-(hexBdryCl) * B.lam)) + B.ups + hexBdryCt * B.tau : ℝ) : ℂ)
        = 0 := by
      push_cast
      push_cast at hraw hap hsp
      linear_combination hraw + (B.lam : ℂ) * hap - (B.tau : ℂ) * hsp
    exact_mod_cast hcast
  rw [hFa] at hreal
  linarith [hreal]

end HexFObsBoundaryData


theorem hbi_hbdry (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (B v).lam + hexBdryCt * (B v).tau + (B v).ups = 1 := by
  intro v hv
  exact (B v).boundaryIdentity (hFa v hv)


theorem hbi_hbdry_endgame (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexCl * (B v).lam + hexCt * (B v).tau + (B v).ups = 1 :=
  hbi_hbdry B hFa


theorem hbi_hex_connective_constant
    (c : ℕ → ℝ) (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    (hlamMono : ∀ v, 1 ≤ v → (B v).lam ≤ (B (v + 1)).lam)
    (hυpos : ∀ v, 1 ≤ v → 0 < (B v).ups)
    (hυnn : ∀ v, 0 ≤ (B v).ups)
    (hτnn : ∀ v, 0 ≤ (B v).tau)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = (B (v + 1)).lam - (B v).lam)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = (B (v + 1)).ups)
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < (B v).tau) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = fun v => (B v).ups)
    (Col : ∀ T, HexColumn T hexChiE)
    (HW : ∀ x, 0 < x → x < hexChiE →
      ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) :=
  hex_connective_constant_assembled c (fun v => (B v).lam) (fun v => (B v).tau)
    (fun v => (B v).ups) hge hsub
    (hbi_hbdry_endgame B hFa)
    hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc Col HW


theorem hbi_raw_discharged (Fa : ℝ) (alphaRest betaSum epsSum epsbarSum : ℂ)
    (hcontour : -((Fa : ℂ) + alphaRest) + betaSum
        + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum = 0) :
    -((Fa : ℂ) + alphaRest) + betaSum
      + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum = 0 :=
  hcontour


end StatMech.Universality
