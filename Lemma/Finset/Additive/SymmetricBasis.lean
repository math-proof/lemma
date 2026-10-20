import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Additive.SymmetricBasis
open Finset


/--
[exists_add_eq_of_image_sub_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/SymmetricBasis.lean)
-/
@[path]
private lemma exists_add_eq_of_image_sub_eq_self_eq
  {A : Finset ℕ}
  {a : ℕ}
-- given
  (hsymm : A.image (fun x => a - x) = A)
  (hadmissible : ∀ m : ℕ, m ≤ a → ∃ x ∈ A, ∃ y ∈ A, x + y = m) :
-- imply
  ∀ m : ℕ, m ≤ 2 * a → ∃ x ∈ A, ∃ y ∈ A, x + y = m := by
-- proof
  apply Finset.exists_add_eq_of_image_sub_eq_self A a hsymm hadmissible


-- created on 2026-10-20
