import Mathlib.Analysis.Normed.Lp.PiLp
import sympy.vector.euclidean

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

namespace LpSpace

variable {p d : ℕ}

-- the same coordinates read in the Euclidean space (rl: `toL2`)
def toL2 (x : LpSpace p d) : EuclideanVec d :=
  WithLp.toLp 2 (WithLp.ofLp x)

-- read Euclidean coordinates as an ℓ^p vector (inverse of `toL2`; rl: implicit, the types coincide there)
def ofL2 (p : ℕ) (x : EuclideanVec d) : LpSpace p d :=
  WithLp.toLp p (WithLp.ofLp x)

@[simp]
lemma toL2_ofL2 (x : EuclideanVec d) : (ofL2 p x).toL2 = x := rfl

@[simp]
lemma ofL2_toL2 (x : LpSpace p d) : ofL2 p x.toL2 = x := rfl

-- ½ ‖x‖ₚ² (rl: `half_sq_Lp`)
noncomputable def half_sq (x : LpSpace p d) : ℝ :=
  1 / 2 * ‖x‖ ^ 2

-- the gradient of `half_sq`: i ↦ ‖x‖ₚ^(2-p) |xᵢ|^(p-2) xᵢ (rl: `half_sq_Lp'`)
noncomputable def half_sq' (x : LpSpace p d) : LpSpace p d :=
  WithLp.toLp p fun i => ‖x‖ ^ (2 - (p : ℝ)) * |x i| ^ ((p : ℝ) - 2) * x i

end LpSpace