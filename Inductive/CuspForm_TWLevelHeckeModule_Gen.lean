import Mathlib
set_option autoImplicit false


namespace CuspForm.TWLevel

inductive Gen (L : ℕ) (S : Set ℕ) (t : ℕ) : Type
  | T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L)
  | U (i : Fin t)

end CuspForm.TWLevel
