import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Lp.lpHolder
/-!
# Separable Banach spaces are quotients of `ℓ¹`

Every separable real Banach space is the image of a surjective bounded linear map from
`lp (fun _ : ℕ => ℝ) 1`.
-/


namespace FunctionalAnalysis.L1Quotient

/-- Radial projection of `E` into its open unit ball. -/
noncomputable def rho {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : E :=
  (1 + ‖v‖)⁻¹ • v

end FunctionalAnalysis.L1Quotient
