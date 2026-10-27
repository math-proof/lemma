import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Class.Probability.Process.GeneratorMatrix
import Structure.Dynamics.ActorCritic.Part6
import Structure.Probability.Process.FrozenInvariantLaw.Part2
open Matrix NormedSpace MeasureTheory

universe u

variable {S : Type u} [Fintype S] [DecidableEq S] {d : ℕ}

/-!
# Frozen invariant law of a policy-indexed generator family (Proposition 5)

Ported from `DynsysFormalization/FrozenInvariantLaw/{Core, Resolvent, Existence, Projection}.lean`
(Notes on Dynamical Systems for Actor-Critic Learning, `formalization/`).

`Q : EuclideanVec d → Matrix S S ℝ` is a generator family indexed by the actor parameter; all
assumptions are imposed on the actor box `actor_box d r`. `ℓ¹` norms are written `∑ i, |x i|` and
zero mass `∑ i, ξ i = 0` (source: `l1Norm`, `ZeroMass`).

* `GeneratorAdjointLipschitzOnBox r Q lQ`: `‖μ Q_θ - μ Q_θ'‖₁ ≤ lQ ‖θ - θ'‖ ‖μ‖₁` on the box.
* `ShortNoteGeneratorAssumptions r Q` (Assumption 1, `ass:gen`): generators on the box, Lipschitz
  constant `lQ ≥ 0`, `0 < r`, a nonempty state space. The source also carries positivity of the
  scalars `tau`, `lambdaC`, `delta` and of `k` from `BoxedFiniteStateData`; they are not used by
  Proposition 5.
* `BoxedShortNoteAssumptions data Q`: `ShortNoteGeneratorAssumptions data.rTheta Q` for a boxed
  model `data : BoxedFiniteStateData S A d m`, plus `Nonempty A`, `0 < data.delta`, `0 < data.lambdaC`.
* `FrozenAdjointSemigroup r Q`: a linear semigroup `t ↦ T θ t` preserving the simplex on the box,
  whose simplex fixed points are exactly the invariant laws.
* `UniformExponentialMixing r Q` (Assumption 4, `ass:mix`): such a semigroup solving the frozen
  law equation, with `‖T θ t ξ‖₁ ≤ cMix e^{-γ t} ‖ξ‖₁` on zero-mass `ξ`, `1 ≤ cMix`, `0 < γ`.
* `UniformExponentialMixing.resolvent θ ξ = -∫_{t>0} T θ t ξ dt` (source: `resolventIntegral`).
* `FrozenResolventWitness`: a right inverse of `ξ ↦ ξ Q_θ` on zero mass with the `cMix/γ` bound.
* `FrozenInvariantLawWitness`: invariant law map, uniqueness, and the `cMix lQ / γ` Lipschitz bound
  (the conclusion of Proposition 5, `prop:invlaw`).
* `MatrixExponentialMixingBound r Q cMix γ`: the paper-literal `ass:mix` for the matrix exponential,
  `‖ξ ᵥ* exp (t • Q θ)‖₁ ≤ cMix e^{-γ t} ‖ξ‖₁`.
-/


-- paper-literal `ass:mix` for the matrix exponential (source: `MatrixExponentialMixingBound`)
class MatrixExponentialMixingBound (r : ℝ) (Q : EuclideanVec d → Matrix S S ℝ) (cMix γ : ℝ) : Prop where
  bound : ∀ θ ∈ actor_box d r, ∀ ξ : S → ℝ, ∑ i, ξ i = 0 → ∀ t, 0 ≤ t →
    ∑ i, |(ξ ᵥ* exp (t • Q θ)) i| ≤ cMix * Real.exp (-γ * t) * ∑ i, |ξ i|

