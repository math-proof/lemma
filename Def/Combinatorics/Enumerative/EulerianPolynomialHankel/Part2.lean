/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
public import Theorem.Finset.Enumerative.HeilermannWeightedMotzkinDeterminant
public import Theorem.Combinatorics.Enumerative.EulerianPolynomialHankel

@[expose] public section

section

namespace MetaMathlibExt

noncomputable def ehd_b (k : ℕ) : Polynomial ℤ :=
  Polynomial.C (k + 1 : ℤ) + Polynomial.C (k : ℤ) * Polynomial.X

noncomputable def ehd_lambda (k : ℕ) : Polynomial ℤ :=
  Polynomial.C ((k : ℤ) ^ 2) * Polynomial.X

noncomputable def ehd_table : ℕ → ℕ → Polynomial ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => ehd_table m 0 + Polynomial.X * ehd_table m 1
  | m + 1, k + 1 =>
      ehd_table m k + ehd_b (k + 1) * ehd_table m (k + 1) +
        ehd_lambda (k + 2) * ehd_table m (k + 2)

end MetaMathlibExt
end
