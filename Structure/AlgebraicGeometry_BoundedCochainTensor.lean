import Mathlib
import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Instance.AlgebraicGeometry_DoubleComplex
import Instance.AlgebraicGeometry_BiCech

set_option autoImplicit false

noncomputable section

universe u

open TensorProduct AlgebraicGeometry


namespace CochainCx

structure Bounded (R : Type u) [CommRing R] where

  X : ℕ → Type u
  [abGrp : ∀ n, AddCommGroup (X n)]
  [modR : ∀ n, Module R (X n)]

  d : ∀ n, X n →ₗ[R] X (n + 1)
  d_sq : ∀ n, d (n + 1) ∘ₗ d n = 0

  N : ℕ
  hBound : ∀ n, N ≤ n → Subsingleton (X n)

attribute [instance] Bounded.abGrp Bounded.modR

namespace Bounded

variable {R : Type u} [CommRing R] (C D : Bounded R)


end Bounded

end CochainCx

end
