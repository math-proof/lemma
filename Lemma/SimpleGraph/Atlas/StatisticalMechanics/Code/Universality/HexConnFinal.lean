import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexConnFinal
open StatMech StatMech.Universality


/--
[hexConnFinal_bdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnFinal.lean)
-/
@[path]
private lemma hexConnFinal_bdry_eq
  {a : ℕ → ℂ}
-- given
  (h0 : ℕ → ℤ)
  (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v)))
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
-- imply
  ∀ v, 1 ≤ v → hexCl * hexConnFinalLam B v + hexCt * hexConnFinalTau B v + hexConnFinalUps B v = 1 := by
-- proof
  apply StatMech.Universality.hexConnFinal_bdry a h0 B hFa

/--
[hex_connective_constant_final](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnFinal.lean)
-/
@[path]
private lemma hex_connective_constant_final_eq
  {c : ℕ → ℝ}
  {a : ℕ → ℂ}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hsub : Submultiplicative c)
  (h0 : ℕ → ℤ)
  (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v)))
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
  (hlamMono : ∀ v, 1 ≤ v → hexConnFinalLam B v ≤ hexConnFinalLam B (v + 1))
  (hυpos : ∀ v, 1 ≤ v → 0 < hexConnFinalUps B v)
  (hυnn : ∀ v, 0 ≤ hexConnFinalUps B v)
  (hτnn : ∀ v, 0 ≤ hexConnFinalTau B v)
  (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = hexConnFinalLam B (v + 1) - hexConnFinalLam B v)
  (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = hexConnFinalUps B (v + 1))
  (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hτdiv : (∃ v, 1 ≤ v ∧ 0 < hexConnFinalTau B v) → ¬ Summable Eτ.wtContour)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυc : Eυ.fiberSum = hexConnFinalUps B)
  (Col : ∀ T, HexColumn T hexChiE)
  (HW : ∀ x, 0 < x → x < hexChiE → ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hex_connective_constant_final c hge hsub a h0 B hFa hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc Col HW

/--
[hexConnFinal_residue_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnFinal.lean)
-/
@[path]
private lemma hexConnFinal_residue_satisfiable_eq :
-- imply
  ∃ lam tau ups Fa : ℝ, hexCl * lam + hexCt * tau + ups = 1 ∧ Fa = 1 ∧ 0 < ups ∧ 0 ≤ ups ∧ 0 ≤ tau := by
-- proof
  apply StatMech.Universality.hexConnFinal_residue_satisfiable


-- created on 2026-10-23
