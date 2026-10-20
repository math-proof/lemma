import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Schnirelmann
open Finset
open scoped Pointwise
open MathlibExt.Combinatorics.Schnirelmann


/--
[_root_.schnirelmannDensity_add_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Schnirelmann.lean)
-/
@[path]
private lemma schnirelmannDensity_add_lower_bound_eq
  {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] [DecidablePred (· ∈ A + B)]
-- given
  (hA : 0 ∈ A)
  (hB : 0 ∈ B) :
-- imply
  schnirelmannDensity A + schnirelmannDensity B -
    schnirelmannDensity A * schnirelmannDensity B ≤
    schnirelmannDensity (A + B) := by
-- proof
  apply schnirelmannDensity_add_lower_bound hA hB

/--
[_root_.exists_additive_basis_of_pos_schnirelmannDensity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Schnirelmann.lean)
-/
@[path]
private lemma exists_additive_basis_of_pos_schnirelmannDensity_eq
  {A : Set ℕ} [DecidablePred (· ∈ A)]
-- given
  (hA : 0 ∈ A)
  (hσ : 0 < schnirelmannDensity A) :
-- imply
  ∃ h : ℕ, ∀ n : ℕ, ∃ x : Fin h → ℕ,
    (∀ i, x i ∈ A) ∧ n = ∑ i, x i := by
-- proof
  apply exists_additive_basis_of_pos_schnirelmannDensity hA hσ


-- created on 2026-10-20
