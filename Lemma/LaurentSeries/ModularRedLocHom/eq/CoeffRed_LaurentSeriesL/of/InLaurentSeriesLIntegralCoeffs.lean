import Mathlib
import sympy.Basic
import Lemma.ModularCurve.CharPReduction
import Lemma.Int.P2MUtil

open ModularCurve ModularCurve.CharPReduction

/--
[ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed.lean)
-/

private lemma redLoc_eq_coeffRed
  {L : Type*}
  [CommRing L]
  {k : Type*}
  [Field k]
  {A : Subring L}
  {red : A →+* k}
  {R : Subring (LaurentSeries L)}
  {hR : R ≤ integralCoeffs A}
  (f : localizedAtKer A red R hR)
  (hf : (f : LaurentSeries L) ∈ integralCoeffs A) :
  redLoc f = coeffRed A red ⟨(f : LaurentSeries L), hf⟩ := by
  obtain ⟨r, s, hs, hfs⟩ := f.2
  have hmul : coeffRed A red ⟨(f : LaurentSeries L), hf⟩ * redRes A red R hR s = redRes A red R hR r := by
    rw [redRes_apply, redRes_apply, ← map_mul]
    congr 1
    exact Subtype.ext hfs
  have hspec := redLoc_spec f hfs
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := R) (hR := hR) hs
  refine mul_right_cancel₀ hsne (hspec.trans hmul.symm)
@[path]
private lemma main
  [CommRing L] [Field k]
  {A : Subring L}
  {red : A →+* k}
  {N : ℕ} [NeZero N]
  {f : modularLocalized N A red}
-- given
  (hf : (f : LaurentSeries L) ∈ integralCoeffs A) :
-- imply
  modularRedLocHom N A red f = coeffRed A red ⟨(f : LaurentSeries L), hf⟩ :=
-- proof
  redLoc_eq_coeffRed f hf


-- created on 2026-10-23
