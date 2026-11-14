import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Mathlib_Algebra_IsDirectLimit
import Class.Mathlib_Algebra_IsDirectLimit
import Def.Mathlib_Algebra_IsDirectLimit
import Theorem.Mathlib_Algebra_IsDirectLimit

namespace Definitions
end Definitions

namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}
  (f : (i j : ι) → (h : i ≤ j) → M i → M j)
  {P₁ P₂ : Type*} (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)
  [DirectedSystem M f]

@[path, simp]
private lemma Equiv_apply (i : ι) (x : M i) [IsDirectLimit f g₁] [IsDirectLimit f g₂] :
  Equiv f g₁ g₂ (g₁ i x) = g₂ i x := by
  simp [Equiv, Equiv.coe_fn_mk, compatibility', implies_true, lift_of]

end IsDirectLimit
