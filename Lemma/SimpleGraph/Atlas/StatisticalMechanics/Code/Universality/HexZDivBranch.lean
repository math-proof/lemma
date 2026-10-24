import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexZDivBranch
open StatMech StatMech.Universality


/--
[hexZDiv_sqrt_gt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivBranch.lean)
-/
@[path]
private lemma hexZDiv_sqrt_gt_one_eq :
-- imply
  1 < Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hexZDiv_sqrt_gt_one

/--
[hexZDiv_chiSq_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivBranch.lean)
-/
@[path]
private lemma hexZDiv_chiSq_lt_one_eq :
-- imply
  hexChiE * hexChiE < 1 := by
-- proof
  apply StatMech.Universality.hexZDiv_chiSq_lt_one

/--
[hexZDiv_chi_bound_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivBranch.lean)
-/
@[path]
private lemma hexZDiv_chi_bound_fails_eq
  {g : ℕ} :
-- imply
  ¬ (hexChiE ^ g ≤ hexChiE * hexChiE ^ (g + 1)) := by
-- proof
  apply StatMech.Universality.hexZDiv_chi_bound_fails g

/--
[hexZDiv_contour_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivBranch.lean)
-/
@[path]
private lemma hexZDiv_contour_limits_eq
  {lam tau ups : ℕ → ℝ}
-- given
  (hbdry : ∀ h, hexBdryCl * lam h + hexBdryCt * tau h + ups h = 1)
  (hlamMono : Monotone lam)
  (hupsMono : Monotone ups)
  (hlamNN : ∀ h, 0 ≤ lam h)
  (hupsNN : ∀ h, 0 ≤ ups h)
  (htauNN : ∀ h, 0 ≤ tau h) :
-- imply
  ∃ Llam Ltau Lups : ℝ, Tendsto lam atTop (𝓝 Llam) ∧ Tendsto tau atTop (𝓝 Ltau) ∧ Tendsto ups atTop (𝓝 Lups) ∧ hexBdryCl * Llam + hexBdryCt * Ltau + Lups = 1 := by
-- proof
  apply StatMech.Universality.hexZDiv_contour_limits lam tau ups hbdry hlamMono hupsMono hlamNN hupsNN htauNN

/--
[hexZDiv_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivBranch.lean)
-/
@[path]
private lemma hexZDiv_branch_eq
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
  apply StatMech.Universality.hexZDiv_branch c lam tau ups hbdry hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc

/--
[hexZDiv_branch_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZDivBranch.lean)
-/
@[path]
private lemma hexZDiv_branch_full_eq
  {c : ℕ → ℝ}
  {lamW tauW upsW : ℕ → ℝ}
  {lam tau ups : ℕ → ℝ}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
-- given
  (hbdryWidth : ∀ h, hexBdryCl * lamW h + hexBdryCt * tauW h + upsW h = 1)
  (hlamMonoW : Monotone lamW)
  (hupsMonoW : Monotone upsW)
  (hlamNNW : ∀ h, 0 ≤ lamW h)
  (hupsNNW : ∀ h, 0 ≤ upsW h)
  (htauNNW : ∀ h, 0 ≤ tauW h)
  (hbdryScale : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
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
  (∃ Llam Ltau Lups : ℝ, Tendsto lamW atTop (𝓝 Llam) ∧ Tendsto tauW atTop (𝓝 Ltau) ∧ Tendsto upsW atTop (𝓝 Lups) ∧ hexBdryCl * Llam + hexBdryCt * Ltau + Lups = 1) ∧ ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexZDiv_branch_full c lamW tauW upsW hbdryWidth hlamMonoW hupsMonoW hlamNNW hupsNNW htauNNW lam tau ups hbdryScale hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc


-- created on 2026-10-23
