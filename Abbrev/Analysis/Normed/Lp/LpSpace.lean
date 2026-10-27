import Mathlib.Analysis.Normed.Lp.PiLp
import Abbrev.Analysis.InnerProductSpace.EuclideanVec


/-!
# `ℓ^p` coordinate vectors

Ported from rl-theory-in-lean `RLTheory/StochasticApproximation/LpSpace.lean`.

* `LpSpace p d` is `ℝ^d` with the `ℓ^p` norm (`p : ℕ`), i.e. Mathlib's `PiLp p (fun _ : Fin d => ℝ)`.
* `LpSpace.toL2 x` reads the same coordinates as a Euclidean vector. Since `PiLp` is a `WithLp`
  structure this is the explicit `WithLp.toLp 2 (WithLp.ofLp x)` (rl: `toL2`, a bare coercion).
* `LpSpace.ofL2 p v` is the inverse reading `WithLp.toLp p (WithLp.ofLp v)`.
* `LpSpace.half_sq x = ½ ‖x‖ₚ²` (rl: `half_sq_Lp`) and `LpSpace.half_sq' x`, its gradient
  `i ↦ ‖x‖ₚ^(2-p) |xᵢ|^(p-2) xᵢ` (rl: `half_sq_Lp'`).
-/

-- ℝ^d with the ℓ^p norm (rl: `StochasticApproximation.LpSpace p d`)
abbrev LpSpace (p d : ℕ) := PiLp p fun _ : Fin d => ℝ

