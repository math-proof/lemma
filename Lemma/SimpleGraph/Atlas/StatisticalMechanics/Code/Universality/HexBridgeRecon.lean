import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
open StatMech StatMech.Universality StatMech.Universality.HexHWDataRecon


/--
[hexChiE_inv_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexChiE_inv_pos_eq :
-- imply
  0 < hexChiE⁻¹ := by
-- proof
  apply StatMech.Universality.hexChiE_inv_pos

/--
[hexCut_numVertices_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexCut_numVertices_sum_eq
  {a₁ a₂ : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 h1 : ℤ)
  (hcp : cp ≤ ts.length) :
-- imply
  (HexWalk.ofTurns a₁ h0 (ts.take cp)).numVertices + (HexWalk.ofTurns a₂ h1 (ts.drop cp)).numVertices = (HexWalk.ofTurns a₁ h0 ts).numVertices + 1 := by
-- proof
  apply StatMech.Universality.hexCut_numVertices_sum a₁ a₂ h0 h1 ts cp hcp

/--
[hexCut_pow_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexCut_pow_factor_eq
  {a₁ a₂ : ℂ}
  {x : ℝ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 h1 : ℤ)
  (hx : 0 < x)
  (hcp : cp ≤ ts.length) :
-- imply
  x ^ (HexWalk.ofTurns a₁ h0 ts).numVertices = x⁻¹ * (x ^ (HexWalk.ofTurns a₁ h0 (ts.take cp)).numVertices * x ^ (HexWalk.ofTurns a₂ h1 (ts.drop cp)).numVertices) := by
-- proof
  apply StatMech.Universality.hexCut_pow_factor a₁ a₂ h0 h1 x hx ts cp hcp

/--
[hexHighestCut_weight_bound_literal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexHighestCut_weight_bound_literal_eq
  {a a₂ : ℂ}
  {x : ℝ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 h2 : ℤ)
  (hx : 0 < x)
  (hcp : cp ≤ ts.length)
  (hleg1 : (HexWalk.ofTurns a h0 ts).IsLegalSAW → (HexWalk.ofTurns a h0 (ts.take cp)).IsLegalSAW)
  (hleg2 : (HexWalk.ofTurns a h0 ts).IsLegalSAW → (HexWalk.ofTurns a₂ h2 (ts.drop cp)).IsLegalSAW) :
-- imply
  hexSAWwt a h0 x ts ≤ x⁻¹ * (hexSAWwt a h0 x (ts.take cp) * hexSAWwt a₂ h2 x (ts.drop cp)) := by
-- proof
  apply StatMech.Universality.hexHighestCut_weight_bound_literal a a₂ h0 h2 x hx ts cp hcp hleg1 hleg2

/--
[hexRec_term_of_cut_recon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexRec_term_of_cut_recon_eq
  {lam ups : ℕ → ℝ}
  {v : ℕ}
  {Cut : HexHighestCut hexChiE⁻¹}
-- given
  (hD : (∑' d, Cut.wtγ d) = lam (v + 1) - lam v)
  (hB : (∑' b, Cut.wtB b) = ups (v + 1)) :
-- imply
  lam (v + 1) - lam v ≤ hexChiE⁻¹ * (ups (v + 1)) ^ 2 := by
-- proof
  apply StatMech.Universality.hexRec_term_of_cut_recon lam ups v Cut hD hB

/--
[hexZ_chi_div_recon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexZ_chi_div_recon_eq
  {c lam tau ups : ℕ → ℝ}
-- given
  (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
  (hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE⁻¹ * (ups (v + 1)) ^ 2)
  (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
  (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
  (hυnn : ∀ v, 0 ≤ ups v)
  (hτnn : ∀ v, 0 ≤ tau v)
  (hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable (fun n => c n * hexChiE ^ n))
  (hυemb : Summable (fun n => c n * hexChiE ^ n) → Summable ups) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexZ_chi_div_recon c lam tau ups hbdry hrec hlamMono hυpos hυnn hτnn hτcol hυemb

/--
[hexZ_chi_div_from_geometry_recon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexZ_chi_div_from_geometry_recon_eq
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
  apply StatMech.Universality.hexZ_chi_div_from_geometry_recon c lam tau ups hbdry hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc

/--
[hexHW_two_overcount_pow_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexHW_two_overcount_pow_factor_eq
  {x : ℝ}
  {g m n : ℕ}
-- given
  (hx : 0 < x)
  (hmn : m + n = g + 2) :
-- imply
  x ^ g = (x ^ 2)⁻¹ * (x ^ m * x ^ n) := by
-- proof
  apply StatMech.Universality.hexHW_two_overcount_pow_factor x hx g m n hmn

/--
[partial_bound_recon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma partial_bound_recon_eq
  {c υ : ℕ → ℝ}
  {x : ℝ}
  {N : ℕ}
  {H : HexHWDataRecon c υ x N} :
-- imply
  ∑ n ∈ Finset.range N, c n * x ^ n ≤ 2 * (x ^ 2)⁻¹ * (∏' T, (1 + υ T)) ^ 2 := by
-- proof
  apply StatMech.Universality.HexHWDataRecon.partial_bound_recon H

/--
[hexZ_conv_recon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexZ_conv_recon_eq
  {c upsx : ℕ → ℝ}
  {x : ℝ}
-- given
  (hx : 0 < x)
  (hc : ∀ n, 0 ≤ c n)
  (hbridge : ∀ N, ∑ n ∈ Finset.range N, c n * x ^ n ≤ 2 * (x ^ 2)⁻¹ * (∏' T, (1 + upsx T)) ^ 2) :
-- imply
  Summable (fun n => c n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexZ_conv_recon c upsx x hx hc hbridge

/--
[hexZ_conv_recon_from_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean)
-/
@[path]
private lemma hexZ_conv_recon_from_geometry_eq
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
  apply StatMech.Universality.hexZ_conv_recon_from_geometry c x hx hlt hc C H


-- created on 2026-10-23
