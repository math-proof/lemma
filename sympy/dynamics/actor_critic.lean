import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import sympy.stats.stochastic_process_types
import sympy.vector.euclidean

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
open Matrix

universe u v

-- the actor box [-r, r]^d (source: `InActorBox`)
def actor_box (d : ℕ) (r : ℝ) : Set (EuclideanVec d) :=
  {θ | ∀ j, |θ j| ≤ r}

-- coordinatewise projection onto the actor box (source: `actorBoxProjection`)
noncomputable def actor_box_projection {d : ℕ} (r : ℝ) (θ : EuclideanVec d) : EuclideanVec d :=
  WithLp.toLp 2 fun j => max (-r) (min r (θ j))

-- forward-time law equation δ μ' = μ Q_{θ(t)} (source: `Level1.ForwardSolvesStateEquation`)
structure ForwardSolvesStateEquation {S : Type u} [Fintype S] {d : ℕ} (δ : ℝ)
    (Q : EuclideanVec d → Matrix S S ℝ) (θ : ℝ → EuclideanVec d) (μ : ℝ → S → ℝ) : Prop where
  cont : Continuous μ
  hasDeriv : ∀ t, 0 ≤ t → HasDerivWithinAt μ (δ⁻¹ • (μ t ᵥ* Q (θ t))) (Set.Ici t) t

-- boxed finite-state actor-critic model (source: `BoxedFiniteStateData`, `Level1Dims`, `Level1Scalars`)
structure BoxedFiniteStateData (S : Type u) (A : Type v) [Fintype S] [Fintype A] (d m : ℕ) where
  rTheta : ℝ
  tau : ℝ
  lambdaC : ℝ
  delta : ℝ
  reward : S → A → ℝ
  actorFeature : S → A → EuclideanVec d
  criticFeature : S → A → EuclideanVec m

-- phase point (θ, w, μ) (source: `PhasePoint`)
abbrev PhasePoint (d m : ℕ) (S : Type u) := EuclideanVec d × EuclideanVec m × (S → ℝ)

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

-- bounded subsets of the phase space (source: `PhaseBounded`)
structure PhaseBounded (data : BoxedFiniteStateData S A d m) (B : Set (PhasePoint d m S)) : Prop where
  subset : B ⊆ phase_space data
  bounded : ∃ M, 0 ≤ M ∧ ∀ x ∈ B, ‖x.2.1‖ ≤ M
end

-- continuous semiflow on α (source: `ContinuousSemiflow`)
structure ContinuousSemiflow (α : Type u) [TopologicalSpace α] where
  toFun : ℝ → α → α
  map_zero' : ∀ x, toFun 0 x = x
  map_add' : ∀ t s, 0 ≤ t → 0 ≤ s → ∀ x, toFun (t + s) x = toFun t (toFun s x)
  continuous_apply : ∀ t, 0 ≤ t → Continuous (toFun t)
  continuous_trajectory : ∀ x, Continuous fun t => toFun t x

-- invariant set: T(t) K = K for t ≥ 0 (source: `Invariant`)
def ContinuousSemiflow.Invariant {α : Type u} [TopologicalSpace α] (Φ : ContinuousSemiflow α) (K : Set α) : Prop :=
  ∀ t, 0 ≤ t → Φ.toFun t '' K = K

-- A attracts B (source: `Attracts`)
def ContinuousSemiflow.Attracts {α : Type u} [TopologicalSpace α] (Φ : ContinuousSemiflow α) (B K : Set α) : Prop :=
  ∀ U, IsOpen U → K ⊆ U → ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → ∀ x ∈ B, Φ.toFun t x ∈ U

section
variable {S : Type u} {A : Type v} [Fintype S] [Fintype A] {d m : ℕ}

-- K absorbs every phase-bounded set (source: `Absorbs`)
def ContinuousSemiflow.Absorbs (data : BoxedFiniteStateData S A d m) (Φ : ContinuousSemiflow (PhasePoint d m S)) (K : Set (PhasePoint d m S)) : Prop :=
  ∀ B, PhaseBounded data B → ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → ∀ x ∈ B, Φ.toFun t x ∈ K

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

-- integrating factor exp(∫₀ᵗ a) (source: `Level1.scalarIntegratingFactor`)
noncomputable def scalar_integrating_factor (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ s in (0 : ℝ)..t, a s)

-- absorbing critic radius max 1 (2 Bb / λ) (source: `Level1.criticRadius`)
noncomputable def critic_radius (Bb lambdaC : ℝ) : ℝ :=
  max 1 (2 * (Bb / lambdaC))

-- admissible critic radius (source: `Level1.IsValidCriticRadius`)
structure IsValidCriticRadius (lambdaC Bb rW : ℝ) : Prop where
  lambdaC_pos : 0 < lambdaC
  Bb_nonneg : 0 ≤ Bb
  one_le : 1 ≤ rW
  ratio_le : 2 * (Bb / lambdaC) ≤ rW

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

-- critic equation w' = b - A w (source: `Level1.SolvesCriticEquation`)
structure SolvesCriticEquation {m : ℕ} (A : ℝ → Matrix (Fin m) (Fin m) ℝ) (b w : ℝ → EuclideanVec m) : Prop where
  hasDeriv : ∀ t, HasDerivAt w (critic_velocity A b w t) t

-- forward-time critic equation (source: `Level1.ForwardSolvesCriticEquation`)
structure ForwardSolvesCriticEquation {m : ℕ} (A : ℝ → Matrix (Fin m) (Fin m) ℝ) (b w : ℝ → EuclideanVec m) : Prop where
  cont : Continuous w
  hasDeriv : ∀ t, 0 ≤ t → HasDerivWithinAt w (critic_velocity A b w t) (Set.Ici t) t

-- entry time into the critic ball (source: `Level1.criticBallEntryTime`)
noncomputable def critic_ball_entry_time (lambdaC Bb rW M : ℝ) : ℝ :=
  Real.log (1 + M ^ 2 / (rW ^ 2 - Bb ^ 2 / lambdaC ^ 2)) / lambdaC

-- law equation δ μ' = μ Q_{θ(t)} for all t (source: `Level1.SolvesStateEquation`)
structure SolvesStateEquation {S : Type u} [Fintype S] {d : ℕ} (δ : ℝ) (Q : EuclideanVec d → Matrix S S ℝ) (θ : ℝ → EuclideanVec d) (μ : ℝ → S → ℝ) : Prop where
  hasDeriv : ∀ t, HasDerivAt μ (δ⁻¹ • (μ t ᵥ* Q (θ t))) t
