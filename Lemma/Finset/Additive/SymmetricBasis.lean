import Mathlib
import sympy.Basic
import Lean.Elab.Tactic.Omega


namespace Finset

/--
[exists_add_eq_of_image_sub_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/SymmetricBasis.lean)
-/
@[path]
lemma exists_add_eq_of_image_sub_eq_self
  {A : Finset ℕ}
  {a : ℕ}
-- given
  (hsymm : A.image (fun x => a - x) = A)
  (hadmissible : ∀ m : ℕ, m ≤ a → ∃ x ∈ A, ∃ y ∈ A, x + y = m) :
-- imply
  ∀ m : ℕ, m ≤ 2 * a → ∃ x ∈ A, ∃ y ∈ A, x + y = m := by
-- proof
  have hmax : ∀ x ∈ A, x ≤ a := by
    intro x hx
    rw [← hsymm] at hx
    obtain ⟨y, _, rfl⟩ := mem_image.mp hx
    exact Nat.sub_le _ _
  intro m hm
  by_cases hma : m ≤ a
  · exact hadmissible m hma
  · obtain ⟨x, hx, y, hy, hxy⟩ := hadmissible (2 * a - m) (by omega)
    have hax : a - x ∈ A := by
      rw [← hsymm]
      exact mem_image.mpr ⟨x, hx, rfl⟩
    have hay : a - y ∈ A := by
      rw [← hsymm]
      exact mem_image.mpr ⟨y, hy, rfl⟩
    refine ⟨a - x, hax, a - y, hay, ?_⟩
    have hxle := hmax x hx
    have hyle := hmax y hy
    omega

end Finset


-- created on 2026-10-20
-- updated on 2026-10-23
