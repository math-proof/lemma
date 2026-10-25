import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexConnAssembly
open StatMech StatMech.Universality


/--
[hexConnAssembly_summable_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnAssembly.lean)
-/
@[path]
private lemma hexConnAssembly_summable_zero_eq
  {c : ℕ → ℝ} :
-- imply
  Summable (fun n => c n * (0 : ℝ) ^ n) := by
-- proof
  apply StatMech.Universality.hexConnAssembly_summable_zero c

/--
[hexConnAssembly_conv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnAssembly.lean)
-/
@[path]
private lemma hexConnAssembly_conv_eq
  {c : ℕ → ℝ}
-- given
  (hc : ∀ n, 0 ≤ c n)
  (Col : ∀ T, HexColumn T hexChiE)
  (HW : ∀ x, 0 < x → x < hexChiE → ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
-- imply
  ∀ x, 0 ≤ x → x < hexChiE → Summable (fun n => c n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexConnAssembly_conv c hc Col HW

/--
[hex_connective_constant_assembled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnAssembly.lean)
-/
@[path]
private lemma hex_connective_constant_assembled_eq
  {c lam tau ups : ℕ → ℝ}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hsub : Submultiplicative c)
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
  (hEυc : Eυ.fiberSum = ups)
  (Col : ∀ T, HexColumn T hexChiE)
  (HW : ∀ x, 0 < x → x < hexChiE → ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hex_connective_constant_assembled c lam tau ups hge hsub hbdry hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc Col HW


-- created on 2026-10-23
