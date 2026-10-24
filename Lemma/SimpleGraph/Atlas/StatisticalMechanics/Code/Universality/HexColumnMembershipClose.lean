import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexColumnMembershipClose
open StatMech StatMech.Universality


/--
[hcm_vertex_is_prefix_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_vertex_is_prefix_last_eq
  {a : ℂ}
  {ts : List ℤ}
  {v : ℂ}
-- given
  (h0 : ℤ)
  (hv : v ∈ verticesAux a h0 ts) :
-- imply
  ∃ k ≤ ts.length, v = hexInfra_midAccum a h0 (ts.take k) + HexWalk.halfStep (hexInfra_headAccum h0 (ts.take k)) := by
-- proof
  apply StatMech.Universality.hcm_vertex_is_prefix_last a h0 ts v hv

/--
[hcm_vertex_re_le_cutDisp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_vertex_re_le_cutDisp_eq
  {a : ℂ}
  {ts : List ℤ}
  {v : ℂ}
-- given
  (h0 : ℤ)
  (hv : v ∈ verticesAux a h0 ts) :
-- imply
  v.re ≤ a.re + hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts) := by
-- proof
  apply StatMech.Universality.hcm_vertex_re_le_cutDisp a h0 ts v hv

/--
[hcm_stMid_eq_midAccum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_stMid_eq_midAccum_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hfs_stMid m h ts = hexInfra_midAccum m h ts := by
-- proof
  apply StatMech.Universality.hcm_stMid_eq_midAccum m h ts

/--
[hcm_stHead_eq_headAccum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_stHead_eq_headAccum_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hfs_stHead h ts = hexInfra_headAccum h ts := by
-- proof
  apply StatMech.Universality.hcm_stHead_eq_headAccum h ts

/--
[hcm_first_vertex_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_first_vertex_mem_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  a + halfStep h0 ∈ verticesAux a h0 ts := by
-- proof
  apply StatMech.Universality.hcm_first_vertex_mem a h0 ts

/--
[hcm_dropStart_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_dropStart_re_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  (hfs_stMid a h0 (ts.take cp)).re + (HexWalk.halfStep (hfs_stHead h0 (ts.take cp))).re = a.re + hexW2_partialDisp h0 ts cp := by
-- proof
  apply StatMech.Universality.hcm_dropStart_re a h0 ts cp

/--
[hcm_verticesAux_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_verticesAux_translate_eq
  {δ : ℂ}
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  verticesAux (m + δ) h ts = (verticesAux m h ts).map (· + δ) := by
-- proof
  apply StatMech.Universality.hcm_verticesAux_translate δ m h ts

/--
[hcm_spans_transl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_spans_transl_eq
  {m m' : ℂ}
  {T : ℕ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hcm_SpansWidth m h T ts ↔ hcm_SpansWidth m' h T ts := by
-- proof
  apply StatMech.Universality.hcm_spans_transl m m' h T ts

/--
[hcm_take_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_take_spans_eq
  {a : ℂ}
  {T : ℕ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (hT : (T : ℝ) ≤ hexW2_partialDisp h0 ts cp - (HexWalk.halfStep h0).re) :
-- imply
  hcm_SpansWidth a h0 T (ts.take cp) := by
-- proof
  apply StatMech.Universality.hcm_take_spans a h0 T ts cp hT

/--
[hcm_drop_first_is_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_drop_first_is_max_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (hcp : cp = hexW2_cutPos h0 ts)
  (hcple : cp ≤ ts.length) :
-- imply
  ∀ v ∈ (HexWalk.ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp)) (ts.drop cp)).vertices, v.re ≤ (hfs_stMid a h0 (ts.take cp)).re + (HexWalk.halfStep (hfs_stHead h0 (ts.take cp))).re := by
-- proof
  apply StatMech.Universality.hcm_drop_first_is_max a h0 ts cp hcp hcple

/--
[hcm_drop_not_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_drop_not_reaches_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
  {T : ℕ}
-- given
  (h0 : ℤ)
  (hcp : cp = hexW2_cutPos h0 ts)
  (hcple : cp ≤ ts.length)
  (hT : 1 ≤ T) :
-- imply
  ¬ hexWall3_ReachesWidth (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp)) T (ts.drop cp) := by
-- proof
  apply StatMech.Universality.hcm_drop_not_reaches a h0 ts cp hcp hcple T hT

/--
[hcm_drop_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_drop_spans_eq
  {a : ℂ}
  {T : ℕ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (hdescend : (T : ℝ) ≤ (HexWalk.halfStep (hexInfra_headAccum h0 (ts.take cp))).re - (hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp) + (HexWalk.halfStep (hexInfra_headAccum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp))).re)) :
-- imply
  hcm_SpansWidth (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp)) T (ts.drop cp) := by
-- proof
  apply StatMech.Universality.hcm_drop_spans a h0 T ts cp hdescend

/--
[hcm_hexZ_chi_div_of_descends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_hexZ_chi_div_of_descends_eq
  {c : ℕ → ℝ}
  {a0 : ℂ}
  {tau : ℕ → ℝ}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
-- given
  (h0 : ℤ)
  (memA : ℕ → List ℤ → Prop)
  (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
  (hreach : ∀ v, hcm_CutReaches h0 (v + 1) (fun ts => memA (v + 1) ts ∧ ¬ memA v ts))
  (hdesc : ∀ v, hcm_DropDescends h0 (v + 1) (fun ts => memA (v + 1) ts ∧ ¬ memA v ts))
  (hDsum : ∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} => hexSAWwt a0 h0 hexChiE d.1))
  (hBsum : ∀ v, Summable (fun b : {ts // hcm_BridgeContent a0 (v + 1) ts} => hexSAWwt a0 h0 hexChiE b.1))
  (hAsum : ∀ v, Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a0 h0 hexChiE n.1))
  (hbdry : ∀ v, 1 ≤ v → hexCl * hpb_lamS a0 h0 hexChiE (memA v) + hexCt * tau v + hpb_upsS a0 h0 hexChiE (hcm_BridgeContent a0 v) = 1)
  (hlamMono : ∀ v, 1 ≤ v → hpb_lamS a0 h0 hexChiE (memA v) ≤ hpb_lamS a0 h0 hexChiE (memA (v + 1)))
  (hυpos : ∀ v, 1 ≤ v → 0 < hpb_upsS a0 h0 hexChiE (hcm_BridgeContent a0 v))
  (hτnn : ∀ v, 0 ≤ tau v)
  (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυc : Eυ.fiberSum = fun v => hpb_upsS a0 h0 hexChiE (hcm_BridgeContent a0 v)) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hcm_hexZ_chi_div_of_descends c a0 h0 memA tau hsub hreach hdesc hDsum hBsum hAsum hbdry hlamMono hυpos hτnn Eτ hEτ hτdiv Eυ hEυ hEυc

/--
[hcm_singleRight_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_singleRight_spans_eq
  {a : ℂ} :
-- imply
  hcm_SpansWidth a 0 0 [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hcm_singleRight_spans a

/--
[hcm_singleRight_bridgeContent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean)
-/
@[path]
private lemma hcm_singleRight_bridgeContent_eq
  {a : ℂ} :
-- imply
  hcm_BridgeContent a 0 [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hcm_singleRight_bridgeContent a


-- created on 2026-10-23
