module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Abbrev.Analysis.InnerProductSpace.EuclideanVec
public import Theorem.Analysis.Normed.Lp.LpSpace

@[expose] public section

namespace LpSpace

variable {p d : ℕ}

-- ½ ‖x‖ₚ² (rl: `half_sq_Lp`)
noncomputable def half_sq (x : LpSpace p d) : ℝ :=
  1 / 2 * ‖x‖ ^ 2

-- the gradient of `half_sq`: i ↦ ‖x‖ₚ^(2-p) |xᵢ|^(p-2) xᵢ (rl: `half_sq_Lp'`)
noncomputable def half_sq' (x : LpSpace p d) : LpSpace p d :=
  WithLp.toLp p fun i => ‖x‖ ^ (2 - (p : ℝ)) * |x i| ^ ((p : ℝ) - 2) * x i

end LpSpace
