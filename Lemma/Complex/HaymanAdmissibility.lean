import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.HaymanAdmissibility

open Complex.HaymanAdmissibility

/--
[hayman_coefficient_asymptotic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/HaymanAdmissibility.lean)
-/
@[path]
private lemma hayman_coefficient_asymptotic_eq
-- given
  (G : ℂ → ℂ) (coeff : ℕ → ℂ) (R0 ρ : ℝ) (saddle : ℕ → ℝ)
  (hAdm : IsHaymanAdmissible G R0 ρ)
  (hsum : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => coeff n * z ^ n) (G z))
  (hsaddle : ∀ᶠ n : ℕ in Filter.atTop, saddle n ∈ Set.Ioo R0 ρ ∧
    haymanAuxiliaryA G (saddle n) = (n : ℝ) ∧
    (∀ r ∈ Set.Ioo R0 ρ, haymanAuxiliaryA G r = (n : ℝ) → r = saddle n)) :
-- imply
  Asymptotics.IsEquivalent Filter.atTop coeff
    (fun n => G (saddle n : ℂ) /
      ((saddle n : ℂ) ^ n *
        (Real.sqrt (2 * Real.pi * haymanAuxiliaryB G (saddle n)) : ℂ))) := by
-- proof
  apply hayman_coefficient_asymptotic G coeff R0 ρ saddle hAdm hsum hsaddle


-- created on 2026-10-09
