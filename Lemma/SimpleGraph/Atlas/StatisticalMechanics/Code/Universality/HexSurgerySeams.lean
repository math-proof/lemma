import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
open StatMech StatMech.Universality


/--
[hexVerticesAux_take_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexVerticesAux_take_prefix_eq
  {m : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h : ℤ) :
-- imply
  (verticesAux m h (ts.take cp)) <+: (verticesAux m h ts) := by
-- proof
  apply StatMech.Universality.hexVerticesAux_take_prefix m h ts cp

/--
[hexVerticesAux_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexVerticesAux_drop_eq
  {m : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h : ℤ)
  (hcp : cp ≤ ts.length) :
-- imply
  ∃ m', (verticesAux m h ts).drop cp = verticesAux m' (h + (ts.take cp).sum) (ts.drop cp) := by
-- proof
  apply StatMech.Universality.hexVerticesAux_drop m h ts cp hcp

/--
[hexCut_legal_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexCut_legal_take_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (hleg : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (ofTurns a h0 (ts.take cp)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexCut_legal_take a h0 ts cp hleg

/--
[hexCut_legal_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexCut_legal_drop_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (hcp : cp ≤ ts.length)
  (hleg : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (ofTurns (hexDropMid a h0 ts cp) (h0 + (ts.take cp).sum) (ts.drop cp)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexCut_legal_drop a h0 ts cp hcp hleg

/--
[hexZ_chi_div_seams_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexZ_chi_div_seams_closed_eq
  {c lam tau ups : ℕ → ℝ}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
-- given
  (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
  (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
  (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
  (hυnn : ∀ v, 0 ≤ ups v)
  (hτnn : ∀ v, 0 ≤ tau v)
  (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
  (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
  (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυc : Eυ.fiberSum = ups) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexZ_chi_div_seams_closed c lam tau ups hbdry hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc

/--
[hexSeams_powerset_range_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexSeams_powerset_range_tendsto_eq :
-- imply
  Tendsto (fun N => (Finset.range N).powerset) atTop atTop := by
-- proof
  apply StatMech.Universality.hexSeams_powerset_range_tendsto

/--
[hexSeams_prod_one_add_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexSeams_prod_one_add_mono_eq
  {f : ℕ → ℝ}
-- given
  (hnn : ∀ i, 0 ≤ f i) :
-- imply
  Monotone (fun N => ∏ i ∈ Finset.range N, (1 + f i)) := by
-- proof
  apply StatMech.Universality.hexSeams_prod_one_add_mono f hnn

/--
[hexSeams_prod_one_add_le_tprod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexSeams_prod_one_add_le_tprod_eq
  {f : ℕ → ℝ}
  {N : ℕ}
-- given
  (hnn : ∀ i, 0 ≤ f i)
  (hm : Multipliable (fun i => 1 + f i)) :
-- imply
  ∏ i ∈ Finset.range N, (1 + f i) ≤ ∏' i, (1 + f i) := by
-- proof
  apply StatMech.Universality.hexSeams_prod_one_add_le_tprod f hnn hm N

/--
[hexSeams_summable_finset_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexSeams_summable_finset_prod_eq
  {f : ℕ → ℝ}
-- given
  (hnn : ∀ i, 0 ≤ f i)
  (hm : Multipliable (fun i => 1 + f i)) :
-- imply
  Summable (fun t : Finset ℕ => ∏ i ∈ t, f i) := by
-- proof
  apply StatMech.Universality.hexSeams_summable_finset_prod f hnn hm

/--
[tsum_finset_prod_eq_tprod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma tsum_finset_prod_eq_tprod_eq
  {f : ℕ → ℝ}
-- given
  (hnn : ∀ i, 0 ≤ f i)
  (hm : Multipliable (fun i => 1 + f i)) :
-- imply
  (∑' t : Finset ℕ, ∏ i ∈ t, f i) = ∏' i, (1 + f i) := by
-- proof
  apply StatMech.Universality.tsum_finset_prod_eq_tprod f hnn hm

/--
[bridgeSeqOfFinset_widths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma bridgeSeqOfFinset_widths_eq
  {s : Finset ℕ}
-- given
  (hs : ∀ T ∈ s, 0 < T) :
-- imply
  (bridgeSeqOfFinset s hs).map HexBridge.width = (s.sort (· ≤ ·)).reverse := by
-- proof
  apply StatMech.Universality.bridgeSeqOfFinset_widths s hs

/--
[hexSeams_sort_reverse_strictDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexSeams_sort_reverse_strictDecr_eq
  {s : Finset ℕ} :
-- imply
  ((s.sort (· ≤ ·)).reverse).Pairwise (· > ·) := by
-- proof
  apply StatMech.Universality.hexSeams_sort_reverse_strictDecr s

/--
[bridgeSeqOfFinset_strictDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma bridgeSeqOfFinset_strictDecr_eq
  {s : Finset ℕ}
-- given
  (hs : ∀ T ∈ s, 0 < T) :
-- imply
  StrictDecreasingWidths (bridgeSeqOfFinset s hs) := by
-- proof
  apply StatMech.Universality.bridgeSeqOfFinset_strictDecr s hs

/--
[bridgeSeq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma bridgeSeq_prod_eq
  {s : Finset ℕ}
  {υ : ℕ → ℝ}
-- given
  (hs : ∀ T ∈ s, 0 < T) :
-- imply
  ((bridgeSeqOfFinset s hs).map (fun b => υ b.width)).prod = ∏ T ∈ s, υ T := by
-- proof
  apply StatMech.Universality.bridgeSeq_prod s hs υ

/--
[hexZ_conv_seams_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean)
-/
@[path]
private lemma hexZ_conv_seams_closed_eq
  {c : ℕ → ℝ}
  {x : ℝ}
-- given
  (hx : 0 < x)
  (hlt : x < hexChiE)
  (hc : ∀ n, 0 ≤ c n)
  (C : ∀ T, HexColumn T hexChiE)
  (H : ∀ N, HexHWDataRecon c (fun T => (C T).colSum x) x N) :
-- imply
  Summable (fun n => c n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexZ_conv_seams_closed c x hx hlt hc C H


-- created on 2026-10-23
