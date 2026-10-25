import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexZDivTauClose.Part4
open StatMech StatMech.Universality


/--
[hzd_not_summable_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean)
-/
@[path]
private lemma hzd_not_summable_const_eq
  {c : ℝ}
-- given
  (hc : c ≠ 0) :
-- imply
  ¬ Summable (fun _ : ℕ => c) := by
-- proof
  apply StatMech.Universality.hzd_not_summable_const hc

/--
[hzd_not_summable_of_const_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean)
-/
@[path]
private lemma hzd_not_summable_of_const_inj_eq
  {w : I → ℝ}
  {c : ℝ}
  {g : ℕ → I}
-- given
  (hc : 0 < c)
  (hg : Function.Injective g)
  (hconst : ∀ n, w (g n) = c) :
-- imply
  ¬ Summable w := by
-- proof
  apply StatMech.Universality.hzd_not_summable_of_const_inj w c hc g hg hconst

/--
[hzd_vertShift_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean)
-/
@[path]
private lemma hzd_vertShift_injective_eq
  {mid period : ℂ}
-- given
  (hp : period ≠ 0) :
-- imply
  Function.Injective (fun h : ℕ => mid + period * (h : ℂ)) := by
-- proof
  apply StatMech.Universality.hzd_vertShift_injective mid period hp

/--
[hzd_sawwt_vertShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean)
-/
@[path]
private lemma hzd_sawwt_vertShift_eq
  {mid period : ℂ}
  {x : ℝ}
  {turns : List ℤ}
-- given
  (head : ℤ)
  (h : ℕ) :
-- imply
  hexSAWwt (mid + period * (h : ℂ)) head x turns = hexSAWwt mid head x turns := by
-- proof
  apply StatMech.Universality.hzd_sawwt_vertShift mid period head x turns h

/--
[hzd_tau_side_diverges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean)
-/
@[path]
private lemma hzd_tau_side_diverges_eq
  {Iτ : Type}
  {tau : ℕ → ℝ}
  {S : HexSideContour Iτ tau} :
-- imply
  (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable S.Eτ.wtContour := by
-- proof
  apply StatMech.Universality.hzd_tau_side_diverges S

/--
[hzd_hexZ_chi_div_tauClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean)
-/
@[path]
private lemma hzd_hexZ_chi_div_tauClosed_eq
  {c lam tau ups : ℕ → ℝ}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
  {Iτ : Type}
  {S : HexSideContour Iτ tau}
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
  (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυc : Eυ.fiberSum = ups) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hzd_hexZ_chi_div_tauClosed c lam tau ups hbdry hlamMono hυpos hυnn hτnn Cut hCutD hCutB S hEτ Eυ hEυ hEυc

/--
[hzd_trivial_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean)
-/
@[path]
private lemma hzd_trivial_wt_eq :
-- imply
  hexSAWwt (0 : ℂ) 0 hexChiE [] = hexChiE := by
-- proof
  apply StatMech.Universality.hzd_trivial_wt

/--
[hzd_witnessE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean)
-/
@[path]
private lemma hzd_witnessE_eq
-- given
  (h : ℕ) :
-- imply
  hzd_witnessEτ.wtContour h = hexChiE := by
-- proof
  apply StatMech.Universality.hzd_witnessE h

/--
[hzd_sideContour_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivTauClose.lean)
-/
@[path]
private lemma hzd_sideContour_fires_eq :
-- imply
  ¬ Summable hzd_witnessEτ.wtContour := by
-- proof
  apply StatMech.Universality.hzd_sideContour_fires


-- created on 2026-10-23
