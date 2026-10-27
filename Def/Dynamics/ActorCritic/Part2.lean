import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Instance.Probability.Process.StochasticProcessTypes.Part3
import Abbrev.Analysis.InnerProductSpace.EuclideanVec
import Abbrev.Dynamics.ActorCritic
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


section

variable {S : Type u} {A : Type v} [Fintype S] [Fintype A] {d m : ℕ}

-- phase space Θ × ℝ^m × Δ_S (source: `InPhaseSpace`, `phaseSpace`)
def phase_space (data : BoxedFiniteStateData S A d m) : Set (PhasePoint d m S) :=
  {x | x.1 ∈ actor_box d data.rTheta ∧ StochasticVec x.2.2}

-- boxed absorbing set Θ × closedBall(0, rW) × Δ_S (source: `absorbingSet`)
def absorbing_set (data : BoxedFiniteStateData S A d m) (rW : ℝ) : Set (PhasePoint d m S) :=
  actor_box d data.rTheta ×ˢ Metric.closedBall 0 rW ×ˢ {μ | StochasticVec μ}

-- phase norm ‖θ‖ + ‖w‖ + ‖μ‖₁ (source: `phaseNorm`)
noncomputable def phase_norm (x : PhasePoint d m S) : ℝ :=
  ‖x.1‖ + ‖x.2.1‖ + ∑ i, |x.2.2 i|

end
