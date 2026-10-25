/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/HaymanAdmissibility.lean -/


import Theorem.Analysis.Complex.HaymanAdmissibility


namespace MathlibExtTest.Analysis.Complex.HaymanAdmissibility

open Asymptotics Filter MetaMathlibExt

-- Hayman's theorem makes the coefficient error negligible relative to its saddle term.
example (G : ℂ → ℂ) (coeff : ℕ → ℂ) (R0 ρ : ℝ) (saddle : ℕ → ℝ)
    (hG : IsHaymanAdmissible G R0 ρ)
    (hsum : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => coeff n * z ^ n) (G z))
    (hsaddle : ∀ᶠ n : ℕ in atTop, saddle n ∈ Set.Ioo R0 ρ ∧
      haymanAuxiliaryA G (saddle n) = (n : ℝ) ∧
      ∀ r ∈ Set.Ioo R0 ρ, haymanAuxiliaryA G r = (n : ℝ) → r = saddle n) :
    ((fun n => coeff n - G (saddle n : ℂ) /
        ((saddle n : ℂ) ^ n *
          (Real.sqrt (2 * Real.pi * haymanAuxiliaryB G (saddle n)) : ℂ))) =o[atTop]
      fun n => G (saddle n : ℂ) /
        ((saddle n : ℂ) ^ n *
          (Real.sqrt (2 * Real.pi * haymanAuxiliaryB G (saddle n)) : ℂ))) := by
  exact (hayman_coefficient_asymptotic G coeff R0 ρ saddle hG hsum hsaddle).isLittleO

end MathlibExtTest.Analysis.Complex.HaymanAdmissibility
