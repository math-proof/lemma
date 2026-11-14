import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Mathlib_Algebra_IsDirectLimit
import Class.Mathlib_Algebra_IsDirectLimit
import Def.Mathlib_Algebra_IsDirectLimit
import Theorem.Mathlib_Algebra_IsDirectLimit
import Lemma.Nat.EqSymmLinearEquiv_FGGG_IXG_IX

namespace Definitions
end Definitions

namespace IsDirectLimit.Module

variable {ι : Type*} [Preorder ι] {M : ι → Type*}
  {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  [DirectedSystem M (f · · ·)] [IsDirected ι (· ≤ ·)]
  {P₁ P₂ : Type*} [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
  (g₁ : ∀ i, M i →ₗ[R] P₁) (g₂ : ∀ i, M i →ₗ[R] P₂)
  [h₁ : IsDirectLimit (f · · ·) (g₁ · ·)]
  [h₂ : IsDirectLimit (f · · ·) (g₂ · ·)]

@[path, simp]
private lemma linearEquiv_symm_apply (i : ι) (x : M i) :
  (linearEquiv f g₁ g₂).symm (g₂ i x) = g₁ i x :=
  Nat.EqSymmLinearEquiv_FGGG_IXG_IX.isDirectLimit.linearEquiv_symm_apply (f · · ·) (g₁ · ·) (g₂ · ·) i x

end IsDirectLimit.Module
