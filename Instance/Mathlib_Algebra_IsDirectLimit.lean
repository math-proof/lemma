-- Carved from Lemma/Definitions/Def_Mathlib_Algebra_IsDirectLimit.lean: instance decls only.
import Mathlib
import Class.Mathlib_Algebra_IsDirectLimit

section

variable {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
  (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)

variable [DirectedSystem M f] [IsDirectLimit f g]

namespace IsDirectLimit

variable {P₁ P₂ : Type*} (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)

namespace Module

variable {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid P] [Module R P] (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  [DirectedSystem M (f · · ·)] [IsDirectLimit (fun ⦃i j⦄ h => f i j h) g] [IsDirected ι (· ≤ ·)]

instance [DecidableEq ι] [Nonempty ι] :
    IsDirectLimit (f · · ·) (Module.DirectLimit.of R ι M f ·) where
  surj := Module.DirectLimit.exists_of
  inj i j mi mj h := by
    apply_fun Module.DirectLimit.linearEquiv _ _ at h
    simp_rw [Module.DirectLimit.linearEquiv_of, Quotient.eq] at h
    exact h
  compatibility i j hij x := Module.DirectLimit.of_f

variable [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]

variable [h₂ : IsDirectLimit (f · · ·) (g₂ · ·)]

end Module

end IsDirectLimit
end
