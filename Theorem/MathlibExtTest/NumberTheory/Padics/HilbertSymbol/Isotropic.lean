/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/HilbertSymbol/Isotropic.lean -/


import Lemma.Nat.Padics.HilbertSymbol.Isotropic
import Instance.MathlibExtTest.NumberTheory.Padics.HilbertSymbol.Isotropic
set_option autoImplicit false


/-!
# Tests for isotropy of unit diagonal forms over `ℚ_[p]`
-/


namespace HilbertSymbol

example (a : Fin 3 → ℤ_[3]ˣ) :
    ∃ x : Fin 3 → ℚ_[3], x ≠ 0 ∧ ∑ i, ((a i : ℤ_[3]) : ℚ_[3]) * (x i) ^ 2 = 0 :=
  diagonal_unit_isotropic 3 (by decide) (by decide) a

example (a : Fin 4 → ℤ_[3]ˣ) :
    ∃ x : Fin 4 → ℚ_[3], x ≠ 0 ∧ ∑ i, ((a i : ℤ_[3]) : ℚ_[3]) * (x i) ^ 2 = 0 :=
  diagonal_unit_isotropic 3 (by decide) (by decide) a

end HilbertSymbol
