import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.FermatPolygonal
open scoped BigOperators
open Nat
open MetaMathlibExt


/--
[exists_eq_add_add_triangular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatPolygonal.lean)
-/
@[path]
private lemma exists_eq_add_add_triangular_eq
  {n : ℕ} :
-- imply
  ∃ x y z : ℕ, n = polygonalNumber 3 x + polygonalNumber 3 y + polygonalNumber 3 z := by
-- proof
  apply Nat.exists_eq_add_add_triangular n

/--
[exists_sum_four_sq_eq_and_sum_eq_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatPolygonal.lean)
-/
@[path]
private lemma exists_sum_four_sq_eq_and_sum_eq_of_odd_eq
  {a b : ℕ}
-- given
  (ha : a % 2 = 1)
  (hb : b % 2 = 1)
  (hba : b ^ 2 < 4 * a)
  (hab : 3 * a < b ^ 2 + 2 * b + 4) :
-- imply
  ∃ s t u v : ℕ, a = s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 ∧ b = s + t + u + v := by
-- proof
  apply Nat.exists_sum_four_sq_eq_and_sum_eq_of_odd ha hb hba hab

/--
[fermat_polygonal_number_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatPolygonal.lean)
-/
@[path]
private lemma fermat_polygonal_number_theorem_eq
  :
-- imply
  ∀ (s n : ℕ), 3 ≤ s →
    ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ s ∧
    n = ∑ i ∈ t, Nat.polygonalNumber s (k i) := by
-- proof
  apply MetaMathlibExt.fermat_polygonal_number_theorem


-- created on 2026-10-20
