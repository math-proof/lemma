import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Instance.Probability.Process.StochasticProcessTypes.Part3
import Abbrev.Analysis.InnerProductSpace.EuclideanVec
import Def.Dynamics.ActorCritic.Part3
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

-- global attractor of the boxed system (source: `IsGlobalAttractor`)
structure IsGlobalAttractor (data : BoxedFiniteStateData S A d m) (Φ : ContinuousSemiflow (PhasePoint d m S)) (K : Set (PhasePoint d m S)) : Prop where
  compact : IsCompact K
  subset : K ⊆ phase_space data
  invariant : Φ.Invariant K
  attracts : ∀ B, PhaseBounded data B → Φ.Attracts B K

end

-- Level 1 actor equation θ_j' = (r - θ_j)(r + θ_j) h_j (source: `Level1.SolvesActorBoxEquation`)
structure SolvesActorBoxEquation {d : ℕ} (r : ℝ) (θ h : ℝ → EuclideanVec d) : Prop where
  cont_theta : ∀ j, Continuous fun t => θ t j
  cont_h : ∀ j, Continuous fun t => h t j
  hasDeriv : ∀ t j, HasDerivAt (fun s => θ s j) ((r - θ t j) * (r + θ t j) * h t j) t

-- forward-time actor equation (source: `Level1.ForwardSolvesActorBoxEquation`)
structure ForwardSolvesActorBoxEquation {d : ℕ} (r : ℝ) (θ h : ℝ → EuclideanVec d) : Prop where
  cont_theta : ∀ j, Continuous fun t => θ t j
  cont_h : ∀ j, Continuous fun t => h t j
  hasDeriv : ∀ t j, 0 ≤ t → HasDerivWithinAt (fun s => θ s j) ((r - θ t j) * (r + θ t j) * h t j) (Set.Ici t) t

