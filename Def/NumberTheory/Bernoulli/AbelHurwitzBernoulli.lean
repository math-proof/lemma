/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/AbelHurwitzBernoulli.lean -/

import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring


section

namespace MetaMathlibExt

open scoped BigOperators

-- Step 2: the two polynomials whose equality encodes the Hurwitz identity.
noncomputable def hurwitzP (u : ℚ) (N : ℕ) : Polynomial ℚ :=
  ∑ a ∈ Finset.range (N + 1),
    Polynomial.C (((Nat.choose N a : ℕ) : ℚ) * (u + (a : ℚ)) ^ a) *
      ((Polynomial.X - Polynomial.C (a : ℚ)) ^ (N - a))

noncomputable def hurwitzQ (u : ℚ) (N : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (N + 1),
    Polynomial.C (((Nat.choose N i : ℕ) : ℚ) * ((Nat.factorial i : ℕ) : ℚ)) *
      ((Polynomial.X + Polynomial.C u) ^ (N - i))

-- Umbral linear functional X^i ↦ B_i.
noncomputable def umbral : Polynomial ℚ →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun i => LinearMap.mulRight ℚ (_root_.bernoulli i))

end MetaMathlibExt
end
