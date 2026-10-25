/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/HilbertSymbol/Units.lean -/


import Def.NumberTheory.Padics.HilbertSymbol.Units
import Lemma.Nat.Padics.HilbertSymbol.Units
import Instance.MathlibExtTest.NumberTheory.Padics.HilbertSymbol.Units
set_option autoImplicit false


/-!
# Tests for Hilbert symbols of p-adic integer units
-/


namespace HilbertSymbol

example :
    (unitZpToQp (p := 3) (1 : ℤ_[3]ˣ) : ℚ_[3]) =
      (((1 : ℤ_[3]ˣ) : ℤ_[3]) : ℚ_[3]) :=
  unitZpToQp_coe (1 : ℤ_[3]ˣ)

example :
    ∃ (x₀ y₀ : ℤ_[3]) (z₀ : ℤ_[3]ˣ),
      (z₀ : ℤ_[3]) ^ 2 =
        ((1 : ℤ_[3]ˣ) : ℤ_[3]) * x₀ ^ 2 +
          ((1 : ℤ_[3]ˣ) : ℤ_[3]) * y₀ ^ 2 :=
  chevalley_warning_hensel_lift 3 (by decide) 1 1

example :
    padicHilbertSymbol 3
      (unitZpToQp (1 : ℤ_[3]ˣ))
      (unitZpToQp (1 : ℤ_[3]ˣ)) = 1 :=
  hilbert_symbol_units_eq_one_of_odd 3 (by decide) 1 1

end HilbertSymbol
