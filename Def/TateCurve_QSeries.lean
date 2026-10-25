import Mathlib

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]


section CoeffSum

variable (c : ℕ → ℕ) (q : K)

def term (n : ℕ) : K := (c n : K) * (q ^ n / (1 - q ^ n))


variable {q}


variable [CompleteSpace K]


variable (q) in

noncomputable def coeffSum : K := ∑' n, term c q n

end CoeffSum

section Coefficients

variable [CompleteSpace K]

def b (n : ℕ) : ℕ := (5 * n ^ 3 + 7 * n ^ 5) / 12


variable (q : K)

noncomputable def a₄ : K := -(coeffSum (fun n => 5 * n ^ 3) q)

noncomputable def a₆ : K := -(coeffSum b q)

end Coefficients

section Curve

variable (q : K)

noncomputable def curve : WeierstrassCurve K := ⟨1, 0, 0, a₄ q, a₆ q⟩

end Curve

end TateCurve
