import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose
open StatMech StatMech.Universality StatMech.Universality.HexFObsBoundaryData


/--
[hbi_alphaPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean)
-/
@[path]
private lemma hbi_alphaPhase_eq :
-- imply
  (Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I) + Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)) / 2 = ((-(hexBdryCl) : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hbi_alphaPhase

/--
[hbi_slantPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean)
-/
@[path]
private lemma hbi_slantPhase_eq :
-- imply
  (hbi_j * Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I) + (starRingEnd ℂ) hbi_j * Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I)) / 2 = ((hexBdryCt : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hbi_slantPhase

/--
[hbi_betaPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean)
-/
@[path]
private lemma hbi_betaPhase_eq :
-- imply
  Complex.exp ((-(hbi_sigma * 0) : ℝ) * Complex.I) = 1 := by
-- proof
  apply StatMech.Universality.hbi_betaPhase

/--
[boundaryIdentity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean)
-/
@[path]
private lemma boundaryIdentity_eq
  {B : HexFObsBoundaryData}
-- given
  (hFa : B.Fa = 1) :
-- imply
  hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = 1 := by
-- proof
  apply StatMech.Universality.HexFObsBoundaryData.boundaryIdentity B hFa

/--
[hbi_hbdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean)
-/
@[path]
private lemma hbi_hbdry_eq
  {B : ℕ → HexFObsBoundaryData}
-- given
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
-- imply
  ∀ v, 1 ≤ v → hexBdryCl * (B v).lam + hexBdryCt * (B v).tau + (B v).ups = 1 := by
-- proof
  apply StatMech.Universality.hbi_hbdry B hFa

/--
[hbi_hbdry_endgame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean)
-/
@[path]
private lemma hbi_hbdry_endgame_eq
  {B : ℕ → HexFObsBoundaryData}
-- given
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
-- imply
  ∀ v, 1 ≤ v → hexCl * (B v).lam + hexCt * (B v).tau + (B v).ups = 1 := by
-- proof
  apply StatMech.Universality.hbi_hbdry_endgame B hFa

/--
[hbi_hex_connective_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean)
-/
@[path]
private lemma hbi_hex_connective_constant_eq
  {c : ℕ → ℝ}
  {B : ℕ → HexFObsBoundaryData}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hsub : Submultiplicative c)
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
  (hlamMono : ∀ v, 1 ≤ v → (B v).lam ≤ (B (v + 1)).lam)
  (hυpos : ∀ v, 1 ≤ v → 0 < (B v).ups)
  (hυnn : ∀ v, 0 ≤ (B v).ups)
  (hτnn : ∀ v, 0 ≤ (B v).tau)
  (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = (B (v + 1)).lam - (B v).lam)
  (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = (B (v + 1)).ups)
  (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hτdiv : (∃ v, 1 ≤ v ∧ 0 < (B v).tau) → ¬ Summable Eτ.wtContour)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυc : Eυ.fiberSum = fun v => (B v).ups)
  (Col : ∀ T, HexColumn T hexChiE)
  (HW : ∀ x, 0 < x → x < hexChiE → ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hbi_hex_connective_constant c hge hsub B hFa hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc Col HW

/--
[hbi_raw_discharged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean)
-/
@[path]
private lemma hbi_raw_discharged_eq
  {Fa : ℝ}
  {alphaRest betaSum epsSum epsbarSum : ℂ}
-- given
  (hcontour : -((Fa : ℂ) + alphaRest) + betaSum + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum = 0) :
-- imply
  -((Fa : ℂ) + alphaRest) + betaSum + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum = 0 := by
-- proof
  apply StatMech.Universality.hbi_raw_discharged Fa alphaRest betaSum epsSum epsbarSum hcontour

/--
[hbi_witness_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean)
-/
@[path]
private lemma hbi_witness_identity_eq :
-- imply
  hexBdryCl * hbi_witness.lam + hexBdryCt * hbi_witness.tau + hbi_witness.ups = 1 := by
-- proof
  apply StatMech.Universality.hbi_witness_identity


-- created on 2026-10-23
