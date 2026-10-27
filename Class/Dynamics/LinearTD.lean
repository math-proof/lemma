import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Def.Dynamics.MarkovRewardProcess.Part4
import Abbrev.Analysis.InnerProductSpace.EuclideanVec
import Def.Dynamics.LinearTD
open Finset
open scoped Matrix

universe u

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


-- linear TD iterates driven by samples ω : ℕ → S × S (rl: `LinearTD.LinearTDIterates`)
class LinearTDIterates {S : Type u} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {d : ℕ} (spec : LinearTDSpec S d)
    (w : ℕ → (ℕ → S × S) → EuclideanVec d) : Prop where
  init : ∀ ω, w 0 ω = spec.w₀
  step : ∀ n ω, w (n + 1) ω = w n ω + spec.α n • spec.update (w n ω) (ω (n + 1))

