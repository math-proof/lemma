/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean -/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.NumberTheory.SelbergSieve
import Lemma.Nat.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals.Part3
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
