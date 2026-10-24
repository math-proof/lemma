/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ChebyshevThetaLowerBound.lean -/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Real

/-- Building block: `x ^ (1/2) + x ^ (1/3) + x ^ (1/5)`. -/
private noncomputable def MetaChebyPf (x : ℝ) : ℝ :=
  x ^ (2:ℝ)⁻¹ + x ^ (3:ℝ)⁻¹ + x ^ (5:ℝ)⁻¹

/-- Building block: `½ x ^ (1/4) + ⅓ x ^ (1/6) + ⅕ x ^ (1/10)`. -/
private noncomputable def MetaChebyMf (x : ℝ) : ℝ :=
  (2:ℝ)⁻¹ * x ^ ((4:ℝ)⁻¹) + (3:ℝ)⁻¹ * x ^ ((6:ℝ)⁻¹) + (5:ℝ)⁻¹ * x ^ ((10:ℝ)⁻¹)

/-- Explicit lower bound for `Chebyshev.theta`, obtained from the Costa–Pereira
inequality together with `psi_ge'` and `psi_le`. -/
private noncomputable def MetaChebyLB (x : ℝ) : ℝ :=
  (x - 1) * Real.log 2 - Real.log (x + 2) - Real.log 4 * MetaChebyPf x
    - 2 * Real.log x * MetaChebyMf x

private noncomputable def MetaChebydPf (x : ℝ) : ℝ :=
  (2:ℝ)⁻¹ * x ^ ((2:ℝ)⁻¹ - 1) + (3:ℝ)⁻¹ * x ^ ((3:ℝ)⁻¹ - 1) + (5:ℝ)⁻¹ * x ^ ((5:ℝ)⁻¹ - 1)

private noncomputable def MetaChebydMf (x : ℝ) : ℝ :=
  (2:ℝ)⁻¹ * ((4:ℝ)⁻¹ * x ^ ((4:ℝ)⁻¹ - 1))
    + (3:ℝ)⁻¹ * ((6:ℝ)⁻¹ * x ^ ((6:ℝ)⁻¹ - 1))
    + (5:ℝ)⁻¹ * ((10:ℝ)⁻¹ * x ^ ((10:ℝ)⁻¹ - 1))

private noncomputable def MetaChebydLB (x : ℝ) : ℝ :=
  Real.log 2 - (x + 2)⁻¹ - Real.log 4 * MetaChebydPf x
    - 2 * (x⁻¹ * MetaChebyMf x + Real.log x * MetaChebydMf x)
section
namespace MetaMathlibExt
end MetaMathlibExt
