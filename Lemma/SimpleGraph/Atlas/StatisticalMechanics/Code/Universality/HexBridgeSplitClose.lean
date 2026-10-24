import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexBridgeSplitClose
open StatMech StatMech.Universality


/--
[hbs_highestCut_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeSplitClose.lean)
-/
@[path]
private lemma hbs_highestCut_B_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (memD : List ℤ → Prop)
  (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : Summable (hexW2_halfWt hexChiE)) :
-- imply
  (hbs_highestCut a h0 memD hDsum hBsum).B = HexW2Half := by
-- proof
  apply StatMech.Universality.hbs_highestCut_B a h0 memD hDsum hBsum

/--
[hbs_highestCut_wtB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeSplitClose.lean)
-/
@[path]
private lemma hbs_highestCut_wtB_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (memD : List ℤ → Prop)
  (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : Summable (hexW2_halfWt hexChiE)) :
-- imply
  (hbs_highestCut a h0 memD hDsum hBsum).wtB = hexW2_halfWt hexChiE := by
-- proof
  apply StatMech.Universality.hbs_highestCut_wtB a h0 memD hDsum hBsum

/--
[hbs_highestCut_D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeSplitClose.lean)
-/
@[path]
private lemma hbs_highestCut_D_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (memD : List ℤ → Prop)
  (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : Summable (hexW2_halfWt hexChiE)) :
-- imply
  (hbs_highestCut a h0 memD hDsum hBsum).D = {ts // memD ts} := by
-- proof
  apply StatMech.Universality.hbs_highestCut_D a h0 memD hDsum hBsum

/--
[hbs_highestCut_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeSplitClose.lean)
-/
@[path]
private lemma hbs_highestCut_wt_eq
  {a : ℂ}
  {d : {ts // memD ts}}
-- given
  (h0 : ℤ)
  (memD : List ℤ → Prop)
  (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : Summable (hexW2_halfWt hexChiE)) :
-- imply
  (hbs_highestCut a h0 memD hDsum hBsum).wtγ d = hexSAWwt a h0 hexChiE d.1 := by
-- proof
  apply StatMech.Universality.hbs_highestCut_wt a h0 memD hDsum hBsum d

/--
[hbs_splitFields_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeSplitClose.lean)
-/
@[path]
private lemma hbs_splitFields_closed_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (memD : List ℤ → Prop)
  (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : Summable (hexW2_halfWt hexChiE)) :
-- imply
  (∀ d : {ts // memD ts}, (hbs_highestCut a h0 memD hDsum hBsum).wtB ((hbs_highestCut a h0 memD hDsum hBsum).split d).1 = hexSAWwt a h0 hexChiE (d.1.take (hexW2_cutPos h0 d.1))) ∧ (∀ d : {ts // memD ts}, (hbs_highestCut a h0 memD hDsum hBsum).wtB ((hbs_highestCut a h0 memD hDsum hBsum).split d).2 = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1)) (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) hexChiE (d.1.drop (hexW2_cutPos h0 d.1))) ∧ Function.Injective (hbs_highestCut a h0 memD hDsum hBsum).split := by
-- proof
  apply StatMech.Universality.hbs_splitFields_closed a h0 memD hDsum hBsum

/--
[hbs_hexZ_chi_div_split_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeSplitClose.lean)
-/
@[path]
private lemma hbs_hexZ_chi_div_split_closed_eq
  {c : ℕ → ℝ}
  {Iτ : Type}
  {tau : ℕ → ℝ}
  {S : HexSideContour Iτ tau}
  {Iυ Ila : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
  {Ela : HexColumnEmb ℕ Ila}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
-- given
  (hτnn : ∀ v, 0 ≤ tau v)
  (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
  (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
  (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
  (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
  (hbdry : ∀ v, 1 ≤ v → hexCl * hbr_lamCum (Ela.fiberSum) v + hexCt * tau v + Eυ.fiberSum v = 1)
  (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
  (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hbs_hexZ_chi_div_split_closed c S hτnn Eυ Ela Cut eB hwB eD hwD hbdry hυpos hEτ hEυ

/--
[hbs_split_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeSplitClose.lean)
-/
@[path]
private lemma hbs_split_fires_eq
  {a : ℂ} :
-- imply
  hexW2_halfWt hexChiE (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).1 = hexSAWwt a 0 hexChiE ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])) ∧ hexW2_halfWt hexChiE (hexW2_split a 0 hexW2_singleRight_memD hexW2_singleRight_elt).2 = hexSAWwt (hexDropMid a 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)])) (0 + ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])).sum) hexChiE ([(-1 : ℤ)].drop (hexW2_cutPos 0 [(-1 : ℤ)])) ∧ Function.Injective (hexW2_split a 0 hexW2_singleRight_memD) := by
-- proof
  apply StatMech.Universality.hbs_split_fires a


-- created on 2026-10-23
