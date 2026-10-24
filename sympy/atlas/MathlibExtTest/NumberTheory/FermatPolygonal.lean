/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FermatPolygonal.lean -/


import sympy.atlas.NumberTheory.FermatPolygonal
import Lemma.Nat.FermatPolygonal
import Mathlib.Tactic


namespace MathlibExtTest.NumberTheory.FermatPolygonal

-- Cauchy's lemma gives four squares with prescribed sum for a concrete pair.
example : ∃ s t u v : ℕ,
    11 = s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 ∧ 5 = s + t + u + v := by
  apply Nat.exists_sum_four_sq_eq_and_sum_eq_of_odd
  all_goals norm_num

-- Eureka and Fermat give concrete triangular and pentagonal specializations.
example (n : ℕ) :
    (∃ x y z : ℕ,
      42 = Nat.polygonalNumber 3 x + Nat.polygonalNumber 3 y +
        Nat.polygonalNumber 3 z) ∧
      ∃ (t : Finset ℕ) (k : ℕ → ℕ), t.card ≤ 5 ∧
        n = ∑ i ∈ t, Nat.polygonalNumber 5 (k i) := by
  constructor
  · exact Nat.exists_eq_add_add_triangular 42
  · exact MetaMathlibExt.fermat_polygonal_number_theorem 5 n (by norm_num)

end MathlibExtTest.NumberTheory.FermatPolygonal
