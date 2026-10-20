/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/SymmetricBasis.lean -/

import Mathlib.Data.Finset.Image
import Lean.Elab.Tactic.Omega

namespace Finset

/-- If a finite set `A ⊆ ℕ` lies below `a`, is invariant under `x ↦ a - x`,
and every value through `a` is a sum of two elements of `A`, then every value
through `2 * a` is such a sum.

This is Rohrbach's theorem on symmetric restricted additive bases.

Source: Jukka Kohonen, "A Meet-in-the-Middle Algorithm for Finding Extremal
Restricted Additive 2-Bases", Journal of Integer Sequences 17 (2014), Article
14.6.8, theorem `theorem:symmrest`, lines 274–288, with notation and basis
definitions at lines 226–248,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Kohonen2/kohonen5.tex>. -/
theorem exists_add_eq_of_image_sub_eq_self (A : Finset ℕ) (a : ℕ)
    (hsymm : A.image (fun x => a - x) = A)
    (hadmissible : ∀ m : ℕ, m ≤ a → ∃ x ∈ A, ∃ y ∈ A, x + y = m) :
    ∀ m : ℕ, m ≤ 2 * a → ∃ x ∈ A, ∃ y ∈ A, x + y = m := by
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
