import Mathlib.Algebra.Order.Group.PosPart
import sympy.stats.generator_matrix
import sympy.Basic
import Lemma.GeneratorMatrix.GetVecMul.ge.Zero.of.Eq_0.All_Ge_0.GeneratorMatrix
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {P : Matrix S S ℝ}
  {x : S → ℝ}
  {i : S}
-- given
  (h₀ : GeneratorMatrix P)
  (h₁ : 0 ≤ x i) :
-- imply
  0 ≤ (x⁻ ᵥ* P) i := by
-- proof
  exact GeneratorMatrix.GetVecMul.ge.Zero.of.Eq_0.All_Ge_0.GeneratorMatrix h₀ (fun j => negPart_nonneg (x j)) (negPart_eq_zero.2 h₁)


-- created on 2026-09-26
