import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Instance.Probability.Process.StochasticProcessTypes.Part3
import Abbrev.Analysis.InnerProductSpace.EuclideanVec
import Def.Dynamics.ActorCritic.Part6
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


-- law equation δ μ' = μ Q_{θ(t)} for all t (source: `Level1.SolvesStateEquation`)
structure SolvesStateEquation {S : Type u} [Fintype S] {d : ℕ} (δ : ℝ) (Q : EuclideanVec d → Matrix S S ℝ) (θ : ℝ → EuclideanVec d) (μ : ℝ → S → ℝ) : Prop where
  hasDeriv : ∀ t, HasDerivAt μ (δ⁻¹ • (μ t ᵥ* Q (θ t))) t

