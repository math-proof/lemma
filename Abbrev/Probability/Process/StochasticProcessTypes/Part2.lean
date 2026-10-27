import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Class.Data.Set.Add
import Class.Data.Nat.GCD.Intfunc
import Class.Probability.Process.StochasticProcessTypes
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


-- Probability simplex on S: {x | x ≥ 0, ∑ x = 1} inside l1Space S.
-- Geometrically: a 0-simplex is a point, 1-simplex a segment, 2-simplex a triangle, 3-simplex a tetrahedron, … (here dimension is |S| - 1).
abbrev Simplex (S : Type u) [Fintype S] :=
  {x : l1Space S | StochasticVec (WithLp.ofLp x)}

