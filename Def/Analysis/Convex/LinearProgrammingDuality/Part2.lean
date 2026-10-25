import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Dual
import Theorem.Analysis.Convex.LinearProgrammingDuality.Part2
/-!
# Strong linear programming duality

A feasible bounded-above primal `max { c ⬝ᵥ x | x ≥ 0, A *ᵥ x ≤ b }` attains
its supremum, and there is a dual-feasible `y ≥ 0` with `c ≤ Aᵀ *ᵥ y` and
equal objective value `c ⬝ᵥ x = b ⬝ᵥ y`.

Informal source: George B. Dantzig, *Linear Programming and Extensions*,
Princeton University Press, 1963, strong duality theorem.
-/


namespace Convex.LPDuality

open scoped Topology Matrix

open Finset Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

section Farkas

variable {p q : ℕ}

/-- The LP cone as a proper cone. -/
noncomputable def lpProperCone (M : Matrix (Fin p) (Fin q) ℝ)
    (e : Fin q → ℝ) : ProperCone ℝ ((Fin p → ℝ) × ℝ) where
  carrier := PointedCone.hull ℝ (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ))
  add_mem' := (PointedCone.hull ℝ
    (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ))).add_mem
  zero_mem' := (PointedCone.hull ℝ
    (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ))).zero_mem
  smul_mem' := fun c _ hx => (PointedCone.hull ℝ
    (↑(lpConeGens M e) : Set ((Fin p → ℝ) × ℝ))).smul_mem c.property hx
  isClosed' := isClosed_hull_finset _

end Farkas
end Convex.LPDuality
