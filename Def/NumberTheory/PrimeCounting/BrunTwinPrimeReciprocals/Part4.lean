module
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Def.NumberTheory.SelbergSieve
public import Theorem.Nat.SelbergSieve
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean -/
/-!
# Brun's theorem on twin-prime reciprocals

This file records the convergence of the reciprocal series over twin-prime pairs.
-/
section

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

open MathlibExt.SelbergSieve

-- The sieve, now that N4(a)-(d) are available
noncomputable def brunSieve (Y N : ℕ) : BoundingSieve where
  support := (Finset.range N).image (fun n => n * (n + 2))
  prodPrimes := brunP Y
  prodPrimes_squarefree := brunP_squarefree Y
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (N : ℝ)
  nu := brunNu
  nu_mult := brunNu_mult
  nu_pos_of_prime := by
    intro p hp hdiv
    have hchar := (brunP_prime_dvd Y p hp).mp hdiv
    obtain ⟨hp2, -⟩ := hchar
    rw [brunNu_odd_prime p hp hp2]
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := by
    intro p hp hdiv
    have hchar := (brunP_prime_dvd Y p hp).mp hdiv
    obtain ⟨hp2, -⟩ := hchar
    rw [brunNu_odd_prime p hp hp2]
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast hp.pos
    rw [div_lt_one hp0]
    linarith

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted
end
