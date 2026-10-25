import Mathlib
import Instance.AlgebraicGeometry_DoubleComplex

set_option autoImplicit false

noncomputable section

universe u

namespace DoubleComplex

structure Bounded (R : Type u) [CommRing R] where

  C : ℕ → ℕ → Type u
  [abGrp : ∀ p q, AddCommGroup (C p q)]
  [modR : ∀ p q, Module R (C p q)]

  dH : ∀ p q, C p q →ₗ[R] C (p + 1) q

  dV : ∀ p q, C p q →ₗ[R] C p (q + 1)
  dH_sq : ∀ p q, dH (p + 1) q ∘ₗ dH p q = 0
  dV_sq : ∀ p q, dV p (q + 1) ∘ₗ dV p q = 0

  dHV_comm : ∀ p q, dV (p + 1) q ∘ₗ dH p q = dH p (q + 1) ∘ₗ dV p q

  N : ℕ
  hBound : ∀ p q, N ≤ p ∨ N ≤ q → Subsingleton (C p q)

attribute [instance] Bounded.abGrp Bounded.modR

section Tot

variable {R : Type u} [CommRing R] (D : Bounded R)


end Tot

section DTotGeneric

variable {R : Type u} [CommRing R] {D : Bounded R}


end DTotGeneric

section E2

variable {R : Type u} [CommRing R] (D : Bounded R)


end E2

structure SubQuot (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] where
  Z : Submodule R M
  B : Submodule R M
  hBZ : B ≤ Z

abbrev SubQuot.carrier {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (s : SubQuot R M) : Type u := s.Z ⧸ s.B.comap s.Z.subtype

structure Convergence (R : Type u) [CommRing R]
    (E₂ : ℕ → ℕ → Type u) [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    (H : ℕ → Type u) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] (N : ℕ) where

  Einf : ∀ p q, SubQuot R (E₂ p q)

  hZ0 : ∀ p, (Einf p 0).Z = ⊤

  Bfilt : ∀ p, Fin (N + 1) → Submodule R (E₂ p 0)
  Bfilt_mono : ∀ p, Monotone (Bfilt p)
  Bfilt_bot : ∀ p, Bfilt p 0 = ⊥
  Bfilt_top : ∀ p, Bfilt p (Fin.last N) = (Einf p 0).B

  Bfilt_gr : ∀ p (i : Fin N), ∃ p' q', 1 ≤ q' ∧ ∃ (s : SubQuot R (E₂ p' q')),
    Nonempty (((Bfilt p i.succ) ⧸ (Bfilt p i.castSucc).comap (Bfilt p i.succ).subtype)
      ≃ₗ[R] s.carrier)

  Hfilt : ∀ n, Fin (N + 2) → Submodule R (H n)
  Hfilt_mono : ∀ n, Monotone (Hfilt n)
  Hfilt_bot : ∀ n, Hfilt n 0 = ⊥
  Hfilt_top : ∀ n, Hfilt n (Fin.last (N + 1)) = ⊤

  Hfilt_gr : ∀ (p : Fin (N + 1)),
    Nonempty (((Hfilt (↑p) p.succ) ⧸ (Hfilt (↑p) p.castSucc).comap (Hfilt (↑p) p.succ).subtype)
      ≃ₗ[R] (Einf p 0).carrier)


end DoubleComplex

end
