/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Additive/SymmetricBasis.lean -/

import Lemma.Finset.Additive.SymmetricBasis

example (A : Finset ℕ) (a : ℕ)
    (hsymm : A.image (fun x => a - x) = A)
    (hadmissible : ∀ m : ℕ, m ≤ a → ∃ x ∈ A, ∃ y ∈ A, x + y = m)
    (m : ℕ) (hm : m ≤ 2 * a) :
    ∃ x ∈ A, ∃ y ∈ A, x + y = m :=
  Finset.exists_add_eq_of_image_sub_eq_self A a hsymm hadmissible m hm
