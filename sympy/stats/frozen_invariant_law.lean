import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import sympy.stats.generator_matrix
import sympy.dynamics.actor_critic

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
open Matrix NormedSpace MeasureTheory

universe u

variable {S : Type u} [Fintype S] [DecidableEq S] {d : ℕ}

-- ℓ¹ Lipschitz control of the adjoint generator family on the box (source: `GeneratorAdjointLipschitzOnBox`)
class GeneratorAdjointLipschitzOnBox (r : ℝ) (Q : EuclideanVec d → Matrix S S ℝ) (lQ : ℝ) : Prop where
  lipschitz : ∀ θ ∈ actor_box d r, ∀ θ' ∈ actor_box d r, ∀ μ : S → ℝ,
    ∑ i, |(μ ᵥ* Q θ - μ ᵥ* Q θ') i| ≤ lQ * dist θ θ' * ∑ i, |μ i|

-- Assumption 1 (`ass:gen`) restricted to what Proposition 5 uses (source: `ShortNoteGeneratorAssumptions`)
structure ShortNoteGeneratorAssumptions (r : ℝ) (Q : EuclideanVec d → Matrix S S ℝ) where
  nonempty : Nonempty S
  r_pos : 0 < r
  lQ : ℝ
  lQ_nonneg : 0 ≤ lQ
  generator_on_box : ∀ θ ∈ actor_box d r, GeneratorMatrix (Q θ)
  lipschitz_on_box : GeneratorAdjointLipschitzOnBox r Q lQ

-- short-note generator assumptions on the box of a boxed model, plus positivity of its scalars
-- (source: `ShortNoteGeneratorAssumptions` used together with `BoxedFiniteStateData`)
structure BoxedShortNoteAssumptions {A : Type*} [Fintype A] {m : ℕ} (data : BoxedFiniteStateData S A d m)
    (Q : EuclideanVec d → Matrix S S ℝ) extends ShortNoteGeneratorAssumptions data.rTheta Q where
  nonempty_action : Nonempty A
  delta_pos : 0 < data.delta
  lambdaC_pos : 0 < data.lambdaC

-- frozen adjoint semigroup e^{t Q_θ^*} (source: `FrozenAdjointSemigroup`)
structure FrozenAdjointSemigroup (r : ℝ) (Q : EuclideanVec d → Matrix S S ℝ) where
  toFun : EuclideanVec d → ℝ → (S → ℝ) →L[ℝ] (S → ℝ)
  map_zero' : ∀ θ, toFun θ 0 = ContinuousLinearMap.id ℝ (S → ℝ)
  map_add' : ∀ θ t s, 0 ≤ t → 0 ≤ s → toFun θ (t + s) = (toFun θ t).comp (toFun θ s)
  preserves_simplex : ∀ θ ∈ actor_box d r, ∀ μ, StochasticVec μ → ∀ t, 0 ≤ t →
    StochasticVec (toFun θ t μ)
  fixed_iff_invariantLaw : ∀ θ ∈ actor_box d r, ∀ μ, StochasticVec μ →
    ((∀ t, 0 ≤ t → toFun θ t μ = μ) ↔ InvariantLaw μ (Q θ))

-- Assumption 4 (`ass:mix`), packaged (source: `UniformExponentialMixing`)
structure UniformExponentialMixing (r : ℝ) (Q : EuclideanVec d → Matrix S S ℝ) where
  hQ : ShortNoteGeneratorAssumptions r Q
  cMix : ℝ
  γ : ℝ
  cMix_ge_one : 1 ≤ cMix
  γ_pos : 0 < γ
  semigroup : FrozenAdjointSemigroup r Q
  solves_equation : ∀ θ ∈ actor_box d r, ∀ ξ,
    ForwardSolvesStateEquation 1 Q (fun _ => θ) (fun t => semigroup.toFun θ t ξ)
  mixing : ∀ θ ∈ actor_box d r, ∀ ξ : S → ℝ, ∑ i, ξ i = 0 → ∀ t, 0 ≤ t →
    ∑ i, |semigroup.toFun θ t ξ i| ≤ cMix * Real.exp (-γ * t) * ∑ i, |ξ i|

-- improper-integral resolvent -∫_{t>0} T θ t ξ dt (source: `FrozenSemigroupGeneratorBridge.resolventIntegral`)
noncomputable def UniformExponentialMixing.resolvent {r : ℝ} {Q : EuclideanVec d → Matrix S S ℝ}
    (hMix : UniformExponentialMixing r Q) (θ : EuclideanVec d) (ξ : S → ℝ) : S → ℝ :=
  -∫ t in Set.Ioi (0 : ℝ), hMix.semigroup.toFun θ t ξ

-- right inverse of the adjoint generator on zero mass with the cMix / γ bound (source: `FrozenResolventWitness`)
structure FrozenResolventWitness (r : ℝ) (Q : EuclideanVec d → Matrix S S ℝ)
    (hMix : UniformExponentialMixing r Q) where
  toFun : EuclideanVec d → (S → ℝ) → S → ℝ
  bound : ∀ θ ∈ actor_box d r, ∀ ξ : S → ℝ, ∑ i, ξ i = 0 →
    ∑ i, |toFun θ ξ i| ≤ hMix.cMix / hMix.γ * ∑ i, |ξ i|
  right_inverse : ∀ θ ∈ actor_box d r, ∀ ξ : S → ℝ, ∑ i, ξ i = 0 → toFun θ (ξ ᵥ* Q θ) = ξ

-- conclusion of Proposition 5 (source: `FrozenInvariantLawWitness`)
structure FrozenInvariantLawWitness (r : ℝ) (Q : EuclideanVec d → Matrix S S ℝ)
    (hMix : UniformExponentialMixing r Q) where
  μ : EuclideanVec d → S → ℝ
  invariant : ∀ θ ∈ actor_box d r, InvariantLaw (μ θ) (Q θ)
  unique : ∀ θ ∈ actor_box d r, ∀ ν, InvariantLaw ν (Q θ) → ν = μ θ
  lipschitz : ∀ θ ∈ actor_box d r, ∀ θ' ∈ actor_box d r,
    ∑ i, |μ θ i - μ θ' i| ≤ hMix.cMix * hMix.hQ.lQ / hMix.γ * dist θ θ'

-- paper-literal `ass:mix` for the matrix exponential (source: `MatrixExponentialMixingBound`)
class MatrixExponentialMixingBound (r : ℝ) (Q : EuclideanVec d → Matrix S S ℝ) (cMix γ : ℝ) : Prop where
  bound : ∀ θ ∈ actor_box d r, ∀ ξ : S → ℝ, ∑ i, ξ i = 0 → ∀ t, 0 ≤ t →
    ∑ i, |(ξ ᵥ* exp (t • Q θ)) i| ≤ cMix * Real.exp (-γ * t) * ∑ i, |ξ i|
