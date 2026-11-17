/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/AbelHurwitzBernoulli.lean -/

module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

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
