/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexColumnMembershipClose.Part3


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hcm_hexZ_chi_div_of_descends (c : ℕ → ℝ) (a0 : ℂ) (h0 : ℤ)
    (memA : ℕ → List ℤ → Prop)
    (tau : ℕ → ℝ)
    (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
    (hreach : ∀ v, hcm_CutReaches h0 (v + 1) (fun ts => memA (v + 1) ts ∧ ¬ memA v ts))
    (hdesc : ∀ v, hcm_DropDescends h0 (v + 1) (fun ts => memA (v + 1) ts ∧ ¬ memA v ts))
    (hDsum : ∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} =>
      hexSAWwt a0 h0 hexChiE d.1))
    (hBsum : ∀ v, Summable (fun b : {ts // hcm_BridgeContent a0 (v + 1) ts} =>
      hexSAWwt a0 h0 hexChiE b.1))
    (hAsum : ∀ v, Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a0 h0 hexChiE n.1))
    (hbdry : ∀ v, 1 ≤ v → hexCl * hpb_lamS a0 h0 hexChiE (memA v)
        + hexCt * tau v + hpb_upsS a0 h0 hexChiE (hcm_BridgeContent a0 v) = 1)
    (hlamMono : ∀ v, 1 ≤ v → hpb_lamS a0 h0 hexChiE (memA v)
        ≤ hpb_lamS a0 h0 hexChiE (memA (v + 1)))
    (hυpos : ∀ v, 1 ≤ v → 0 < hpb_upsS a0 h0 hexChiE (hcm_BridgeContent a0 v))
    (hτnn : ∀ v, 0 ≤ tau v)
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = fun v => hpb_upsS a0 h0 hexChiE (hcm_BridgeContent a0 v)) :
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hhe_hexZ_chi_div c a0 h0 memA (fun v => hcm_BridgeContent a0 v) tau hsub
    (fun v => hcm_halvesInColumn_of_descends a0 h0 (v + 1)
      (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (hreach v) (hdesc v))
    hDsum hBsum hAsum hbdry hlamMono hυpos hτnn Eτ hEτ hτdiv Eυ hEυ hEυc


theorem hcm_singleRight_spans (a : ℂ) :
    hcm_SpansWidth a 0 0 [(-1 : ℤ)] := by
  have hdisp : ((0 : ℕ) : ℝ) ≤ hexW2_partialDisp 0 [(-1 : ℤ)] 1 - (HexWalk.halfStep 0).re := by
    rw [hexW2_singleRight_partialDisp_one]
    have hm1 : (HexWalk.halfStep (-1)).re = Real.sqrt 3 / 4 := by
      unfold HexWalk.halfStep hexUnit
      rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((-1 : ℤ) : ℝ)) * ((Real.pi : ℂ) / 3)))
            = ((Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by
              push_cast; ring]
      rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
      push_cast
      rw [show Real.pi / 6 + (-1 : ℝ) * (Real.pi / 3) = -(Real.pi / 6) by ring, Real.cos_neg,
        Real.cos_pi_div_six]
      norm_num; ring
    rw [hm1]
    have : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    push_cast; linarith
  have := hcm_take_spans a 0 0 [(-1 : ℤ)] 1 hdisp
  rwa [show [(-1 : ℤ)].take 1 = [(-1 : ℤ)] from rfl] at this


theorem hcm_singleRight_bridgeContent (a : ℂ) :
    hcm_BridgeContent a 0 [(-1 : ℤ)] :=
  ⟨0, hcm_singleRight_spans a⟩

end StatMech.Universality
