import Mathlib
set_option autoImplicit false


namespace CohCarrier

inductive Gen (M : ℕ) (S : Set ℕ) : Type
  | T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M)
  | U (q : ℕ) (hq : q.Prime) (hqM : q ∣ M)
  | dia (d : (ZMod M)ˣ)

end CohCarrier
