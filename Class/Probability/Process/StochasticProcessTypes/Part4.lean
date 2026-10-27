import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Class.Data.Set.Add
import Class.Data.Nat.GCD.Intfunc
import Instance.Probability.Process.StochasticProcessTypes
open Finset Matrix WithLp Set
open scoped Matrix BigOperators

universe u

/-!
# Stochastic process types (DiscreteMarkovChain)

Empty.Finite discrete-time homogeneous Markov-chain primitives, aligned with
[Instance.Probability.Process.StochasticProcessTypes.Part3.DiscreteMarkovChain](https://github.com/sympy/sympy/blob/master/sympy/stats/stochastic_process_types.py).

In Lean these are typeclasses on a transition matrix `P : Matrix S S ℝ`
(`RowStochastic`, `StochasticIrreducible`, `Aperiodic`) plus the probability
simplex `StochasticVec` / `Simplex`, rather than a single Python class.
-/


-- shared background next-tag floor: every row of P keeps at least mass ε on the same categorical ν
class DoeblinMinorization {S : Type u} [Fintype S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  minorize : ∃ (ε : ℝ) (ν : S → ℝ),
    0 < ε ∧ ε < 1 ∧ StochasticVec ν ∧ ∀ i j, P i j ≥ ε * ν j

-- stationary / equilibrium tag distribution: long-run tag frequencies μ unchanged by one more transition
class Stationary {S : Type u} [Fintype S] (μ : S → ℝ) (P : Matrix S S ℝ) : Prop where
  stationary : μ ᵥ* P = μ

-- no matter how you start to utter, finally you will utter the same kind of stories you like to utter
-- tag mix → stationary μ
-- ρ = forget-rate, geometric convergence to μ
class GeometricMixing {S : Type u} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) [RowStochastic P] : Prop where
  mixing : ∃ (C ρ : ℝ) (μ : S → ℝ),
    0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ StochasticVec μ ∧ Stationary μ P ∧
    ∀ (x : S → ℝ) [StochasticVec x] (n : ℕ),
      (∑ s, |(x ᵥ* (P ^ n) - μ) s|) ≤ C * ρ ^ n

