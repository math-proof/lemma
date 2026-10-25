/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EulerianPolynomialHankel.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
import Lemma.Finset.Enumerative.HeilermannWeightedMotzkinDeterminant


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
