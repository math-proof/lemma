import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Instance.Probability.Process.StochasticProcessTypes.Part3
import Abbrev.Analysis.InnerProductSpace.EuclideanVec
import Structure.Dynamics.ActorCritic.Part4
open Matrix

universe u v

/-!
# Boxed actor-critic phase space: model data, semiflows, attractors and the Level 1 equations

Ported from `DynsysFormalization/Basic.lean` and `DynsysFormalization/Level1/{ActorBox,Critic,Simplex}.lean`
(Notes on Dynamical Systems for Actor-Critic Learning, `formalization/`).

Actor parameters live in `EuclideanVec d` (source: `ActorVec d = Fin d → ℝ`, whose
`actorDistance` is exactly the Euclidean distance), critic parameters in `EuclideanVec m`
(source: `CriticVec m`), state laws are plain vectors `S → ℝ` over a finite state type
(source: `StateLaw n = Fin n → ℝ`).

Basic:
* `BoxedFiniteStateData S A d m`: scalars `rTheta, tau, lambdaC, delta`, reward and features
  (source: `BoxedFiniteStateData`, dimensions/scalars merged from `Level1Dims`, `Level1Scalars`).
* `PhasePoint d m S`, `phase_space data`, `absorbing_set data rW`, `phase_norm`, `PhaseBounded`.
* `ContinuousSemiflow α` with `.Invariant`, `.Attracts`, `.Absorbs`, and `IsGlobalAttractor`.
  Forward invariance is Mathlib's `IsForwardInvariant Φ.toFun K` and the attractor candidate is
  Mathlib's `omegaLimit Filter.atTop Φ.toFun K` (source: `omegaLimitSet`, `tailImage`), so no
  local copies of those notions are kept. `ContinuousSemiflow` itself stays local: Mathlib's
  `Flow` needs an additive monoid acting everywhere with joint continuity, while the source
  semiflow only acts for `t ≥ 0` and is continuous separately in `t` and `x`.

Level 1:
* `actor_box d r`, `actor_box_projection r θ`, `SolvesActorBoxEquation`,
  `ForwardSolvesActorBoxEquation`, `scalar_integrating_factor`.
* `critic_radius`, `IsValidCriticRadius`, `critic_quadratic_form`, `critic_velocity`,
  `ForwardUniformCriticCoercive`, `ForwardUniformCriticDriftBound`, `SolvesCriticEquation`,
  `ForwardSolvesCriticEquation`, `critic_ball_entry_time`.
* `ForwardSolvesStateEquation δ Q θ μ` and `SolvesStateEquation δ Q θ μ`: `δ μ' = μ Q_{θ(t)}`
  (source: stated coordinatewise there; here in vector form via `hasDerivWithinAt_pi`).
-/


-- quadratic form ⟪v, A v⟫ (source: `Level1.criticQuadraticForm`)
noncomputable def critic_quadratic_form {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (v : EuclideanVec m) : ℝ :=
  inner ℝ v (Matrix.toEuclideanLin A v)

-- critic velocity b(t) - A(t) w(t) (source: `Level1.criticVelocity`)
noncomputable def critic_velocity {m : ℕ} (A : ℝ → Matrix (Fin m) (Fin m) ℝ) (b w : ℝ → EuclideanVec m) (t : ℝ) : EuclideanVec m :=
  b t - Matrix.toEuclideanLin (A t) (w t)

-- uniform coercivity λ ‖v‖² ≤ ⟪v, A(t) v⟫ for t ≥ 0 (source: `Level1.ForwardUniformCriticCoercive`)
def ForwardUniformCriticCoercive {m : ℕ} (lambdaC : ℝ) (A : ℝ → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ v, lambdaC * ‖v‖ ^ 2 ≤ critic_quadratic_form (A t) v

-- uniform drift bound ‖b(t)‖ ≤ Bb for t ≥ 0 (source: `Level1.ForwardUniformCriticDriftBound`)
def ForwardUniformCriticDriftBound {m : ℕ} (Bb : ℝ) (b : ℝ → EuclideanVec m) : Prop :=
  ∀ t, 0 ≤ t → ‖b t‖ ≤ Bb

