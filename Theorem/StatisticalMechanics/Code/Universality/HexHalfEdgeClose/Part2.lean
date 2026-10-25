/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part4
import Def.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part2


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


@[simp] theorem hhe_halfClass_lower (a : ℂ) (h0 : ℤ) (x : ℝ) (memD memB : List ℤ → Prop)
    (htake hdrop) (d : {ts // memD ts}) :
    ((hhe_halfClass a h0 x memD memB htake hdrop).lower d).1
      = d.1.take (hexW2_cutPos h0 d.1) := rfl


@[simp] theorem hhe_halfClass_upper (a : ℂ) (h0 : ℤ) (x : ℝ) (memD memB : List ℤ → Prop)
    (htake hdrop) (d : {ts // memD ts}) :
    ((hhe_halfClass a h0 x memD memB htake hdrop).upper d).1
      = d.1.drop (hexW2_cutPos h0 d.1) := rfl


theorem hhe_hexZ_chi_div (c : ℕ → ℝ) (a0 : ℂ) (h0 : ℤ)
    (memA memB : ℕ → List ℤ → Prop) (tau : ℕ → ℝ)
    (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
    (HIC : ∀ v, HexHalvesInColumn h0
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
    ¬ Summable (fun n => c n * hexChiE ^ n) :=
  hpb_hexZ_chi_div c a0 h0 memA memB tau hsub
    (fun v => hhe_halfClass_of_halves a0 h0 hexChiE
      (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1)) (HIC v))
    hDsum hBsum hAsum hbdry hlamMono hυpos hτnn Eτ hEτ hτdiv Eυ hEυ hEυc


theorem hhe_singleRight_cutPos : hexW2_cutPos 0 [(-1 : ℤ)] = 1 := by
  have h1 := hexW2_singleRight_cutPos_pos
  have h2 := hexW2_cutPos_le 0 [(-1 : ℤ)]
  simp only [List.length_cons, List.length_nil] at h2
  omega


end StatMech.Universality
