import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Class.Data.Set.Add
import Class.Data.Nat.GCD.Intfunc
import Class.Probability.Process.StochasticProcessTypes.Part4
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


-- broadcast a vector to a matrix row-wisely
def broadcast {S : Type u} [Fintype S] (ν : S → ℝ) : Matrix S S ℝ :=
  Matrix.of fun _ s' => ν s'

-- the ordinary sample mean of the path, x₀, x₀P, …, x₀Pⁿ
noncomputable def cesaro_average {S : Type u} [Fintype S] [DecidableEq S]
    (x₀ : S → ℝ) [StochasticVec x₀] (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) :
    S → ℝ :=
  (n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* (P ^ k)

