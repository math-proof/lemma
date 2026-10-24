import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexPerScaleBijClose
open StatMech StatMech.Universality


/--
[hpb_tsum_setDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_tsum_setDiff_eq
  {w : List ℤ → ℝ}
-- given
  (P Q : List ℤ → Prop)
  (hsub : ∀ ts, Q ts → P ts)
  (hsumP : Summable (fun n : {ts // P ts} => w n.1)) :
-- imply
  (∑' d : {ts // P ts ∧ ¬ Q ts}, w d.1) = (∑' n : {ts // P ts}, w n.1) - (∑' n : {ts // Q ts}, w n.1) := by
-- proof
  apply StatMech.Universality.hpb_tsum_setDiff P Q w hsub hsumP

/--
[hpb_lamS_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_lamS_nonneg_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (memA : List ℤ → Prop) :
-- imply
  0 ≤ hpb_lamS a h0 x memA := by
-- proof
  apply StatMech.Universality.hpb_lamS_nonneg a h0 hx memA

/--
[hpb_upsS_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_upsS_nonneg_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (memB : List ℤ → Prop) :
-- imply
  0 ≤ hpb_upsS a h0 x memB := by
-- proof
  apply StatMech.Universality.hpb_upsS_nonneg a h0 hx memB

/--
[hpb_cut_wtB_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_cut_wtB_sum_eq
  {a : ℂ}
  {HC : HexHalfClass a h0 hexChiE memD memB}
-- given
  (h0 : ℤ)
  (memD memB : List ℤ → Prop)
  (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
-- imply
  (∑' b, (hpb_cut a h0 memD memB HC hDsum hBsum).wtB b) = hpb_upsS a h0 hexChiE memB := by
-- proof
  apply StatMech.Universality.hpb_cut_wtB_sum a h0 memD memB HC hDsum hBsum

/--
[hpb_cut_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_cut_wt_eq
  {a : ℂ}
  {HC : HexHalfClass a h0 hexChiE memD memB}
-- given
  (h0 : ℤ)
  (memD memB : List ℤ → Prop)
  (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
-- imply
  (∑' d, (hpb_cut a h0 memD memB HC hDsum hBsum).wtγ d) = ∑' d : {ts // memD ts}, hexSAWwt a h0 hexChiE d.1 := by
-- proof
  apply StatMech.Universality.hpb_cut_wt a h0 memD memB HC hDsum hBsum

/--
[hpb_cut_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_cut_wt_eq_2
  {a : ℂ}
  {v : ℕ}
-- given
  (h0 : ℤ)
  (memA : ℕ → List ℤ → Prop)
  (memB : List ℤ → Prop)
  (hsub : ∀ ts, memA v ts → memA (v + 1) ts)
  (HC : HexHalfClass a h0 hexChiE (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) memB)
  (hDsum : Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} => hexSAWwt a h0 hexChiE d.1))
  (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1))
  (hAsum : Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a h0 hexChiE n.1)) :
-- imply
  (∑' d, (hpb_cut a h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) memB HC hDsum hBsum).wtγ d) = hpb_lamS a h0 hexChiE (memA (v + 1)) - hpb_lamS a h0 hexChiE (memA v) := by
-- proof
  apply StatMech.Universality.hpb_cut_wt a h0 memA memB v hsub HC hDsum hBsum hAsum

/--
[hpb_cutB_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_cutB_eq_eq
  {K : ℝ}
  {Cut : HexHighestCut K}
  {a : ℂ}
  {x : ℝ}
  {eB : Cut.B ≃ {ts // memB ts}}
-- given
  (h0 : ℤ)
  (memB : List ℤ → Prop)
  (hwt : ∀ b, Cut.wtB b = hexSAWwt a h0 x (eB b).1) :
-- imply
  (∑' b, Cut.wtB b) = hpb_upsS a h0 x memB := by
-- proof
  apply StatMech.Universality.hpb_cutB_eq Cut a h0 x memB eB hwt

/--
[hpb_hexZ_chi_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_hexZ_chi_div_eq
  {c : ℕ → ℝ}
  {a0 : ℂ}
  {tau : ℕ → ℝ}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
-- given
  (h0 : ℤ)
  (memA memB : ℕ → List ℤ → Prop)
  (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
  (HC : ∀ v, HexHalfClass a0 h0 hexChiE (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1)))
  (hDsum : ∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} => hexSAWwt a0 h0 hexChiE d.1))
  (hBsum : ∀ v, Summable (fun b : {ts // memB (v + 1) ts} => hexSAWwt a0 h0 hexChiE b.1))
  (hAsum : ∀ v, Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a0 h0 hexChiE n.1))
  (hbdry : ∀ v, 1 ≤ v → hexCl * hpb_lamS a0 h0 hexChiE (memA v) + hexCt * tau v + hpb_upsS a0 h0 hexChiE (memB v) = 1)
  (hlamMono : ∀ v, 1 ≤ v → hpb_lamS a0 h0 hexChiE (memA v) ≤ hpb_lamS a0 h0 hexChiE (memA (v + 1)))
  (hυpos : ∀ v, 1 ≤ v → 0 < hpb_upsS a0 h0 hexChiE (memB v))
  (hτnn : ∀ v, 0 ≤ tau v)
  (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυc : Eυ.fiberSum = fun v => hpb_upsS a0 h0 hexChiE (memB v)) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hpb_hexZ_chi_div c a0 h0 memA memB tau hsub HC hDsum hBsum hAsum hbdry hlamMono hυpos hτnn Eτ hEτ hτdiv Eυ hEυ hEυc

/--
[hpb_sidePhaseLock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_sidePhaseLock_eq
  {a : ℂ}
  {z : ℂ}
  {σ x W : ℝ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m))
  (hdett : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = W) :
-- imply
  parafObservable region a h0 z σ x + parafObservable region a h0 (hsc_refl a h0 z) σ x = ((2 * Real.cos (σ * W) * hexClosed_countObs region a h0 z x : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hpb_sidePhaseLock region a h0 z σ x W hsym hdett

/--
[hpb_emptyD_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_emptyD_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  Summable (fun d : {ts // (fun _ : List ℤ => False) ts} => hexSAWwt a h0 x d.1) := by
-- proof
  apply StatMech.Universality.hpb_emptyD_summable a h0 x

/--
[hpb_eD_empty_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_eD_empty_fires_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (P : List ℤ → Prop)
  (hsumP : Summable (fun n : {ts // P ts} => hexSAWwt a h0 x n.1)) :
-- imply
  (∑' d : {ts // P ts ∧ ¬ P ts}, hexSAWwt a h0 x d.1) = hpb_lamS a h0 x P - hpb_lamS a h0 x P := by
-- proof
  apply StatMech.Universality.hpb_eD_empty_fires a h0 x P hsumP

/--
[hpb_eB_empty_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_eB_empty_fires_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (memB : List ℤ → Prop)
  (hBsum : Summable (fun b : {ts // memB ts} => hexSAWwt a h0 hexChiE b.1)) :
-- imply
  (∑' b, (hpb_cut a h0 (fun _ => False) memB (hpb_emptyHalfClass a h0 hexChiE memB) (hpb_emptyD_summable a h0 hexChiE) hBsum).wtB b) = hpb_upsS a h0 hexChiE memB := by
-- proof
  apply StatMech.Universality.hpb_eB_empty_fires a h0 memB hBsum

/--
[hpb_data_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPerScaleBijClose.lean)
-/
@[path]
private lemma hpb_data_satisfiable_eq :
-- imply
  ∃ (a0 : ℂ) (h0 : ℤ) (memA memB : ℕ → List ℤ → Prop), (∀ v ts, memA v ts → memA (v + 1) ts) ∧ (∀ v, Nonempty (HexHalfClass a0 h0 hexChiE (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1)))) ∧ (∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} => hexSAWwt a0 h0 hexChiE d.1)) ∧ (∀ v, Summable (fun b : {ts // memB (v + 1) ts} => hexSAWwt a0 h0 hexChiE b.1)) := by
-- proof
  apply StatMech.Universality.hpb_data_satisfiable


-- created on 2026-10-23
