/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part3


namespace StatMech.Universality

open scoped BigOperators

open Filter Topology


theorem hpb_cut_wtB_sum (a : ℂ) (h0 : ℤ) (memD memB : List ℤ → Prop)
    (HC : HexHalfClass a h0 hexChiE memD memB)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
    (∑' b, (hpb_cut a h0 memD memB HC hDsum hBsum).wtB b)
      = hpb_upsS a h0 hexChiE memB := rfl


theorem hpb_cut_wtγ_sum (a : ℂ) (h0 : ℤ) (memD memB : List ℤ → Prop)
    (HC : HexHalfClass a h0 hexChiE memD memB)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
    (∑' d, (hpb_cut a h0 memD memB HC hDsum hBsum).wtγ d)
      = ∑' d : {ts // memD ts}, hexSAWwt a h0 hexChiE d.1 := rfl


theorem hpb_cut_wtγ_eq_diff (a : ℂ) (h0 : ℤ) (memA : ℕ → List ℤ → Prop) (memB : List ℤ → Prop)
    (v : ℕ) (hsub : ∀ ts, memA v ts → memA (v + 1) ts)
    (HC : HexHalfClass a h0 hexChiE (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) memB)
    (hDsum : Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
      hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1))
    (hAsum : Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a h0 hexChiE n.1)) :
    (∑' d, (hpb_cut a h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) memB HC hDsum hBsum).wtγ d)
      = hpb_lamS a h0 hexChiE (memA (v + 1)) - hpb_lamS a h0 hexChiE (memA v) := by
  rw [hpb_cut_wtγ_sum a h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) memB HC hDsum hBsum]
  unfold hpb_lamS
  exact hpb_tsum_setDiff (memA (v + 1)) (memA v) (hexSAWwt a h0 hexChiE) hsub hAsum


theorem hpb_cutB_eq {K : ℝ} (Cut : HexHighestCut K) (a : ℂ) (h0 : ℤ) (x : ℝ)
    (memB : List ℤ → Prop) (eB : Cut.B ≃ {ts // memB ts})
    (hwt : ∀ b, Cut.wtB b = hexSAWwt a h0 x (eB b).1) :
    (∑' b, Cut.wtB b) = hpb_upsS a h0 x memB := by
  unfold hpb_upsS
  rw [← eB.tsum_eq (fun b => hexSAWwt a h0 x b.1)]
  exact tsum_congr hwt


theorem hpb_hexZ_chi_div (c : ℕ → ℝ) (a0 : ℂ) (h0 : ℤ)
    (memA memB : ℕ → List ℤ → Prop) (tau : ℕ → ℝ)
    (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
    (HC : ∀ v, HexHalfClass a0 h0 hexChiE
      (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1)))
    (hDsum : ∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
      hexSAWwt a0 h0 hexChiE d.1))
    (hBsum : ∀ v, Summable (fun b : {ts // memB (v + 1) ts} => hexSAWwt a0 h0 hexChiE b.1))
    (hAsum : ∀ v, Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a0 h0 hexChiE n.1))
    (hbdry : ∀ v, 1 ≤ v → hexCl * hpb_lamS a0 h0 hexChiE (memA v)
        + hexCt * tau v + hpb_upsS a0 h0 hexChiE (memB v) = 1)
    (hlamMono : ∀ v, 1 ≤ v → hpb_lamS a0 h0 hexChiE (memA v)
        ≤ hpb_lamS a0 h0 hexChiE (memA (v + 1)))
    (hυpos : ∀ v, 1 ≤ v → 0 < hpb_upsS a0 h0 hexChiE (memB v))
    (hτnn : ∀ v, 0 ≤ tau v)
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = fun v => hpb_upsS a0 h0 hexChiE (memB v)) :
    ¬ Summable (fun n => c n * hexChiE ^ n) := by
  
  set Cut : ℕ → HexHighestCut hexChiE⁻¹ := fun v =>
    hpb_cut a0 h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1))
      (HC v) (hDsum v) (hBsum v) with hCut
  
  have hCutD : ∀ v, 1 ≤ v →
      (∑' d, (Cut v).wtγ d)
        = hpb_lamS a0 h0 hexChiE (memA (v + 1)) - hpb_lamS a0 h0 hexChiE (memA v) := by
    intro v _
    exact hpb_cut_wtγ_eq_diff a0 h0 memA (memB (v + 1)) v (hsub v) (HC v)
      (hDsum v) (hBsum v) (hAsum v)
  
  have hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = hpb_upsS a0 h0 hexChiE (memB (v + 1)) := by
    intro v _
    exact hpb_cut_wtB_sum a0 h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1))
      (HC v) (hDsum v) (hBsum v)
  
  exact hexZ_chi_div_seams_closed c
    (fun v => hpb_lamS a0 h0 hexChiE (memA v)) tau (fun v => hpb_upsS a0 h0 hexChiE (memB v))
    hbdry hlamMono hυpos
    (fun v => hpb_upsS_nonneg a0 h0 (le_of_lt hexChiE_pos) (memB v)) hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc


theorem hpb_sidePhaseLock (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x W : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m))
    (hdett : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = W) :
    parafObservable region a h0 z σ x
        + parafObservable region a h0 (hsc_refl a h0 z) σ x
      = ((2 * Real.cos (σ * W) * hexClosed_countObs region a h0 z x : ℝ) : ℂ) :=
  hsc_sidePhaseLock_single region a h0 z σ x W hsym hdett


end StatMech.Universality
