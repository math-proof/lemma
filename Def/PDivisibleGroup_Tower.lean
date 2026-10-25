import Mathlib
import Instance.PDivisibleGroup_Basic

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

universe u v w x

namespace PDivisibleGroup.Hopf

section NSMulBialg

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Bialgebra R A]


variable [Coalgebra.IsCocomm R A]

noncomputable def nsmulBialgHom (n : ℕ) : A →ₐc[R] A := ((toConv (BialgHom.id R A)) ^ n).ofConv

end NSMulBialg

end PDivisibleGroup.Hopf

namespace PDivisibleGroup.Tower

variable {R : Type u} [CommRing R] {L : ℕ → Type v} [∀ w, CommRing (L w)] [∀ w, HopfAlgebra R (L w)]

noncomputable def transitionLE (t : ∀ w, L (w + 1) →ₐc[R] L w) (v : ℕ) : ∀ u : ℕ, L (v + u) →ₐc[R] L v
  | 0 => BialgHom.id R (L v)
  | u + 1 => (transitionLE t v u).comp (t (v + u))

variable (t : ∀ w, L (w + 1) →ₐc[R] L w)


section OfLE

noncomputable def levelCast : ∀ {n m : ℕ}, n = m → (L n ≃ₐc[R] L m)
  | _, _, rfl => BialgEquiv.refl R _


noncomputable def transitionOfLE (a : ℕ) : ∀ b : ℕ, a ≤ b → (L b →ₐc[R] L a)
  | 0, h => ((levelCast (Nat.le_zero.1 h).symm : L 0 ≃ₐc[R] L a) : L 0 →ₐc[R] L a)
  | b + 1, h =>
    if hab : a = b + 1 then ((levelCast hab : L a ≃ₐc[R] L (b + 1)).symm : L (b + 1) →ₐc[R] L a)
    else (transitionOfLE a b (by omega)).comp (t b)

end OfLE

end PDivisibleGroup.Tower
