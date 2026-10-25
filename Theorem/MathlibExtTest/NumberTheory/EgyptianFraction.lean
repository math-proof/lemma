/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/EgyptianFraction.lean -/


import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Def.NumberTheory.EgyptianFraction
import Lemma.Nat.EgyptianFraction
import Def.MathlibExtTest.NumberTheory.EgyptianFraction


namespace EgyptianFractionTest

example : EgyptianFraction.IsNondecreasingUnderapproximation 2 repeated := by
  refine ⟨by norm_num, by norm_num, ⟨by simp [repeated], ?_⟩, by norm_num [repeated]⟩
  intro i j hij
  simp [repeated]

example : EgyptianFraction.IsStrictUnderapproximation 2 increasing := by
  refine ⟨by norm_num, by norm_num, ⟨by simp [increasing], ?_⟩, ?_⟩
  · intro i j hij
    exact Nat.add_lt_add_right hij 2
  · rw [Fin.sum_univ_two]
    change (2 : ℝ)⁻¹ + (3 : ℝ)⁻¹ < 2
    norm_num

example : ¬EgyptianFraction.IsStrictUnderapproximation 2 repeated := by
  intro h
  have hlt := h.strictMono (show (0 : Fin 2) < 1 by decide)
  simp [repeated] at hlt

example : EgyptianFraction.IsStrictUnderapproximation 2 (fun _ : Fin 1 => 2) := by
  refine ⟨by norm_num, by norm_num, ⟨by simp, ?_⟩, ?_⟩
  · intro i j hij
    simp [Fin.eq_zero i, Fin.eq_zero j] at hij
  · rw [Fin.sum_univ_one]
    norm_num

example : ¬EgyptianFraction.IsStrictUnderapproximation 1 (Fin.elim0 : Fin 0 → ℕ) := by
  simp [EgyptianFraction.IsStrictUnderapproximation]

example : ¬EgyptianFraction.IsNondecreasingUnderapproximation 2 (fun _ : Fin 1 => 1) := by
  intro h
  have := h.denominator_ge_two 0
  norm_num at this

example : ¬EgyptianFraction.IsNondecreasingUnderapproximation 1 repeated := by
  intro h
  have := h.sum_lt
  norm_num [repeated, Fin.sum_univ_two] at this

example : ¬EgyptianFraction.IsNondecreasingUnderapproximation 0 repeated := by
  intro h
  have hpos := h.target_pos
  norm_num at hpos

example : ¬EgyptianFraction.IsNondecreasingUnderapproximation 2 decreasing := by
  intro h
  have hle := h.monotone (show (0 : Fin 2) ≤ 1 by decide)
  norm_num [decreasing] at hle

example : ¬EgyptianFraction.IsNondecreasingUnderapproximation 1 (Fin.elim0 : Fin 0 → ℕ) := by
  simp [EgyptianFraction.IsNondecreasingUnderapproximation]

example {n : ℕ} {target : ℝ} {a : Fin n → ℕ}
    (h : EgyptianFraction.IsStrictUnderapproximation target a) :
    EgyptianFraction.IsNondecreasingUnderapproximation target a :=
  h.toIsNondecreasingUnderapproximation

-- Additional sanity checks for the factored 𝓔ₙ predicates
example : EgyptianFraction.IsNondecreasingEgyptian repeated :=
  ⟨by simp [repeated], by intro i j hij; simp [repeated]⟩

example : EgyptianFraction.IsStrictEgyptian increasing :=
  ⟨by simp [increasing], by intro i j hij; exact Nat.add_lt_add_right hij 2⟩

example : ¬EgyptianFraction.IsStrictEgyptian repeated := by
  intro h
  have hlt := h.strictMono (show (0 : Fin 2) < 1 by decide)
  simp [repeated] at hlt

example {n : ℕ} {a : Fin n → ℕ} (h : EgyptianFraction.IsStrictEgyptian a) :
    EgyptianFraction.IsNondecreasingEgyptian a :=
  h.toIsNondecreasingEgyptian

end EgyptianFractionTest
