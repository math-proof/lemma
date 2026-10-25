/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Structure.StatisticalMechanics.Code.Universality.HexZDivTauClose


namespace StatMech.Universality

open Filter Topology Complex HexWalk

open scoped Topology BigOperators


theorem hzd_tau_side_diverges {Iτ : Type} {tau : ℕ → ℝ} (S : HexSideContour Iτ tau) :
    (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable S.Eτ.wtContour := by
  intro hex
  obtain ⟨i₀, hpos⟩ := S.posWit hex
  exact hzd_not_summable_of_const_inj S.Eτ.wtContour (S.Eτ.wtContour i₀) hpos
    (S.shift i₀) (S.shift_inj i₀) (fun n => S.shift_wt i₀ n)


theorem hzd_hexZ_chi_div_tauClosed (c lam tau ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
    (hυnn : ∀ v, 0 ≤ ups v)
    (hτnn : ∀ v, 0 ≤ tau v)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
    {Iτ : Type} (S : HexSideContour Iτ tau)
    (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = ups) :
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hexZ_chi_div_from_geometry_recon c lam tau ups hbdry hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB S.Eτ hEτ (hzd_tau_side_diverges S) Eυ hEυ hEυc


theorem hzd_trivial_wt : hexSAWwt (0 : ℂ) 0 hexChiE [] = hexChiE := by
  rw [hexSAWwt_of_isLegalSAW 0 0 hexChiE (HexWalk.trivialWalk_isLegalSAW 0 0)]
  rw [show (HexWalk.ofTurns (0 : ℂ) 0 []).numVertices = 1 from rfl, pow_one]


end StatMech.Universality
