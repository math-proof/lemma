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

@[expose] public section

section

namespace MetaMathlibExt

/-! # Hankel transform of Eulerian polynomials
-/

def ehd_altSum (m q : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (q + 1),
    (-1 : ℤ) ^ i * (Nat.choose (m + 1) i : ℤ) * ((q - i : ℕ) : ℤ) ^ m

def ehd_coeff (m k : ℕ) : ℤ :=
  ehd_altSum m (m - k)

noncomputable def ehd_poly (m : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (ehd_coeff m k)

end MetaMathlibExt
end
