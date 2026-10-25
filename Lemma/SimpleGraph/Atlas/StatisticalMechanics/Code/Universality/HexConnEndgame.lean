import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
open StatMech StatMech.Universality


/--
[hex_sqrt_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_sqrt_pos_eq :
-- imply
  0 < Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hex_sqrt_pos

/--
[hexChiE_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hexChiE_pos_eq :
-- imply
  0 < hexChiE := by
-- proof
  apply StatMech.Universality.hexChiE_pos

/--
[one_div_hexChi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma one_div_hexChi_eq :
-- imply
  1 / hexChiE = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.one_div_hexChi

/--
[hexCl_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hexCl_pos_eq :
-- imply
  0 < hexCl := by
-- proof
  apply StatMech.Universality.hexCl_pos

/--
[hexCt_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hexCt_pos_eq :
-- imply
  0 < hexCt := by
-- proof
  apply StatMech.Universality.hexCt_pos

/--
[hex_recip_induction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_recip_induction_eq
  {u : ℕ → ℝ}
  {C : ℝ}
-- given
  (hC : 0 < C)
  (hpos : ∀ v, 1 ≤ v → 0 < u v)
  (hmono : ∀ v, 1 ≤ v → u (v + 1) ≤ u v)
  (hrec : ∀ v, 1 ≤ v → u v - u (v + 1) ≤ C * (u (v + 1)) ^ 2) :
-- imply
  ∀ v, 1 ≤ v → 1 / u v ≤ v / min (u 1) (1 / C) := by
-- proof
  apply StatMech.Universality.hex_recip_induction u C hC hpos hmono hrec

/--
[hex_div_of_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_div_of_lower_bound_eq
  {u : ℕ → ℝ}
  {m : ℝ}
-- given
  (hm : 0 < m)
  (hu0 : ∀ n, 0 ≤ u n)
  (hge : ∀ v, 1 ≤ v → m / v ≤ u v) :
-- imply
  ¬ Summable u := by
-- proof
  apply StatMech.Universality.hex_div_of_lower_bound u m hm hu0 hge

/--
[hex_pow_rootid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_pow_rootid_eq
  {c x : ℝ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hc : 0 < c) :
-- imply
  (c ^ ((n : ℝ)⁻¹) * x) ^ n = c * x ^ n := by
-- proof
  apply StatMech.Universality.hex_pow_rootid c x n hn hc

/--
[hex_root_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_root_summable_eq
  {c : ℕ → ℝ}
  {x kappa : ℝ}
-- given
  (hx : 0 ≤ x)
  (hge : ∀ n, 1 ≤ c n)
  (hroot : Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa))
  (hlt : kappa * x < 1) :
-- imply
  Summable (fun n => c n * x ^ n) := by
-- proof
  apply StatMech.Universality.hex_root_summable c x kappa hx hge hroot hlt

/--
[hex_root_not_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_root_not_summable_eq
  {c : ℕ → ℝ}
  {x kappa : ℝ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hroot : Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa))
  (hgt : 1 < kappa * x) :
-- imply
  ¬ Summable (fun n => c n * x ^ n) := by
-- proof
  apply StatMech.Universality.hex_root_not_summable c x kappa hge hroot hgt

/--
[hexZ_chi_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hexZ_chi_div_eq
  {c lam tau ups : ℕ → ℝ}
-- given
  (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
  (hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ hexChiE * (ups (v + 1)) ^ 2)
  (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
  (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
  (hυnn : ∀ v, 0 ≤ ups v)
  (hτnn : ∀ v, 0 ≤ tau v)
  (hτcol : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable (fun n => c n * hexChiE ^ n))
  (hυemb : Summable (fun n => c n * hexChiE ^ n) → Summable ups) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexZ_chi_div c lam tau ups hbdry hrec hlamMono hυpos hυnn hτnn hτcol hυemb

/--
[hex_ups_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_ups_summable_eq
  {upsx : ℕ → ℝ}
  {x : ℝ}
-- given
  (hx : 0 ≤ x)
  (hlt : x < hexChiE)
  (hυnn : ∀ T, 0 ≤ upsx T)
  (hυle : ∀ T, upsx T ≤ (x / hexChiE) ^ T) :
-- imply
  Summable upsx := by
-- proof
  apply StatMech.Universality.hex_ups_summable upsx x hx hlt hυnn hυle

/--
[hex_bridge_multipliable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_bridge_multipliable_eq
  {upsx : ℕ → ℝ}
-- given
  (hsum : Summable upsx) :
-- imply
  Multipliable (fun T => 1 + upsx T) := by
-- proof
  apply StatMech.Universality.hex_bridge_multipliable upsx hsum

/--
[hexZ_conv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hexZ_conv_eq
  {c upsx : ℕ → ℝ}
  {x : ℝ}
-- given
  (hx : 0 ≤ x)
  (hlt : x < hexChiE)
  (hc : ∀ n, 0 ≤ c n)
  (hυnn : ∀ T, 0 ≤ upsx T)
  (hυle : ∀ T, upsx T ≤ (x / hexChiE) ^ T)
  (hbridge : ∀ N, ∑ n ∈ Finset.range N, c n * x ^ n ≤ 2 * (∏' T, (1 + upsx T)) ^ 2) :
-- imply
  Summable (fun n => c n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexZ_conv c upsx x hx hlt hc hυnn hυle hbridge

/--
[hex_kappa_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_kappa_eq_eq
  {c : ℕ → ℝ}
  {kappa : ℝ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hroot : Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa))
  (hdiv : ¬ Summable (fun n => c n * hexChiE ^ n))
  (hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => c n * x ^ n)) :
-- imply
  kappa = 1 / hexChiE := by
-- proof
  apply StatMech.Universality.hex_kappa_eq c kappa hge hroot hdiv hconv

/--
[hex_connective_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnEndgame.lean)
-/
@[path]
private lemma hex_connective_constant_eq
  {c : ℕ → ℝ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hsub : Submultiplicative c)
  (hdiv : ¬ Summable (fun n => c n * hexChiE ^ n))
  (hconv : ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => c n * x ^ n)) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hex_connective_constant c hge hsub hdiv hconv


-- created on 2026-10-23
