/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeSupport.lean -/

import Mathlib.Data.Nat.Prime.Basic

namespace Nat

/-- `SamePrimeSupport a b` states that `a` and `b` are divisible
    by exactly the same prime numbers. -/
def SamePrimeSupport (a b : ℕ) : Prop := ∀ p : ℕ, p.Prime → (p ∣ a ↔ p ∣ b)

theorem samePrimeSupport_refl (a : ℕ) : SamePrimeSupport a a :=
  fun _ _ => Iff.rfl

theorem SamePrimeSupport.symm {a b : ℕ} (h : SamePrimeSupport a b) :
    SamePrimeSupport b a :=
  fun p hp => Iff.symm (h p hp)

theorem SamePrimeSupport.trans {a b c : ℕ} (h1 : SamePrimeSupport a b)
    (h2 : SamePrimeSupport b c) : SamePrimeSupport a c :=
  fun p hp => Iff.trans (h1 p hp) (h2 p hp)

end Nat
