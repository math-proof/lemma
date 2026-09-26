import sympy.stats.stochastic_process_types

/-!
# Generator (rate) matrices of continuous-time finite Markov chains

Ported from `DynsysFormalization/Level1/Simplex.lean` (Notes on Dynamical Systems for Actor-Critic
Learning, `formalization/`).

* `GeneratorMatrix Q`: off-diagonal rates are nonnegative and every row sums to `0`
  (source: `Level1.IsGeneratorMatrix`, which states the diagonal as `Q i i = -∑_{j ≠ i} Q i j`).
* `InvariantLaw μ Q`: `μ` is a probability vector annihilated by the adjoint action,
  `μ ᵥ* Q = 0` (source: `Level1.IsInvariantLaw`, with `generatorAdjointAction Q μ = μ ᵥ* Q`).

The frozen forward evolution `e^{t Q^*}` of the source is the row-vector action
`μ ↦ μ ᵥ* NormedSpace.exp (t • Q)` of Mathlib's matrix exponential.
-/
open Matrix

universe u

-- continuous-time rate matrix: nonnegative off-diagonal rates, zero row sums (source: `Level1.IsGeneratorMatrix`)
class GeneratorMatrix {S : Type u} [Fintype S] (Q : Matrix S S ℝ) : Prop where
  offdiag_nonneg : ∀ i j, i ≠ j → 0 ≤ Q i j
  rowsum : ∀ i, ∑ j, Q i j = 0

-- invariant law of a generator: a probability vector with μ Q = 0 (source: `Level1.IsInvariantLaw`)
class InvariantLaw {S : Type u} [Fintype S] (μ : S → ℝ) (Q : Matrix S S ℝ) : Prop extends StochasticVec μ where
  invariant : μ ᵥ* Q = 0
