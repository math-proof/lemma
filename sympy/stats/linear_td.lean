import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import sympy.stats.markov_reward_process
import sympy.vector.euclidean

/-!
# Linear temporal-difference learning

Ported from rl-theory-in-lean `RLTheory/Algorithm/LinearTD.lean`.

* `LinearTDSpec S d`: a finite MRP together with linearly independent features `x : S → ℝ^d`,
  step sizes `α` and an initial weight `w₀`.
* `LinearTDSpec.update w (s, s') = (r s + γ ⟪x s', w⟫ - ⟪x s, w⟫) x s`, its stationary mean
  `expected_update`, and the SA residual forms `update_target = update + id`,
  `expected_update_target = expected_update + id`.
* `LinearTDSpec.X` (feature matrix), `A = Xᵀ D (γ P - 1) X`, `b = Xᵀ D r` (plain vectors
  `Fin d → ℝ`, weighted by `D = diag μ` without any extra inner product) and the TD fixed point
  `td_fixed_point = -A⁻¹ b`.
* `LinearTDIterates spec w`: `w 0 = w₀`, `w (n+1) = w n + α n · update (w n) (ω (n+1))`.
-/
open Finset
open scoped Matrix

universe u

-- linear TD on a finite MRP (rl: `ReinforcementLearning.LinearTD.LinearTDSpec`)
structure LinearTDSpec (S : Type u) [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (d : ℕ) extends FiniteMRP S where
  x : S → EuclideanVec d
  hx : LinearIndependent ℝ (fun i => fun s => x s i)
  α : ℕ → ℝ
  w₀ : EuclideanVec d

namespace LinearTDSpec

variable {S : Type u} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ} (spec : LinearTDSpec S d)

-- the TD(0) update direction (rl: `LinearTDSpec.update`)
noncomputable def update (w : EuclideanVec d) (y : S × S) : EuclideanVec d :=
  (spec.r y.1 + spec.γ * inner ℝ (spec.x y.2) w - inner ℝ (spec.x y.1) w) • spec.x y.1

-- the SA residual form F w y = update w y + w (rl: `LinearTDSpec.update_target`)
noncomputable def update_target (w : EuclideanVec d) (y : S × S) : EuclideanVec d :=
  spec.update w y + w

-- the feature matrix (rl: `LinearTDSpec.X`)
def X : Matrix S (Fin d) ℝ :=
  fun s i => spec.x s i

section stationary

variable [Nonempty S]

-- the mean update under the stationary pair law μ(s) P(s, s') (rl: `LinearTDSpec.expected_update`)
noncomputable def expected_update (w : EuclideanVec d) : EuclideanVec d :=
  ∑ s, ∑ s', (spec.μ s * spec.P s s') • spec.update w (s, s')

-- f = expected_update + id (rl: `LinearTDSpec.expected_update_target`)
noncomputable def expected_update_target : EuclideanVec d → EuclideanVec d :=
  spec.expected_update + id

-- A = Xᵀ D (γ P - 1) X (rl: `LinearTDSpec.A`)
noncomputable def A : Matrix (Fin d) (Fin d) ℝ :=
  spec.Xᵀ * spec.D * (spec.γ • spec.P - 1) * spec.X

-- b = Xᵀ D r (rl: `LinearTDSpec.b`)
noncomputable def b : Fin d → ℝ :=
  (spec.Xᵀ * spec.D) *ᵥ spec.r

-- the TD fixed point -A⁻¹ b (rl: `LinearTDSpec.td_fixed_point`)
noncomputable def td_fixed_point : EuclideanVec d :=
  WithLp.toLp 2 (-(spec.A⁻¹ *ᵥ spec.b))

end stationary

end LinearTDSpec

-- linear TD iterates driven by samples ω : ℕ → S × S (rl: `LinearTD.LinearTDIterates`)
class LinearTDIterates {S : Type u} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {d : ℕ} (spec : LinearTDSpec S d)
    (w : ℕ → (ℕ → S × S) → EuclideanVec d) : Prop where
  init : ∀ ω, w 0 ω = spec.w₀
  step : ∀ n ω, w (n + 1) ω = w n ω + spec.α n • spec.update (w n ω) (ω (n + 1))