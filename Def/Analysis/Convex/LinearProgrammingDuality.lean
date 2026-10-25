import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Dual
import Theorem.Analysis.Convex.LinearProgrammingDuality
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

/-- LP cone generators: scaled columns, slacks, and the value direction. -/
noncomputable def lpConeGens (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    Finset ((Fin p → ℝ) × ℝ) :=
  (Finset.univ.image (fun i : Fin q => ((fun j => M j i), e i))) ∪
  (Finset.univ.image
    (fun j : Fin p => (Pi.single (M := fun _ => ℝ) j 1, 0))) ∪
  {((0 : Fin p → ℝ), -1)}

/-- The LP cone: image points above achievable values. -/
def lpCone (M : Matrix (Fin p) (Fin q) ℝ) (e : Fin q → ℝ) :
    Set ((Fin p → ℝ) × ℝ) :=
  {zw | ∃ x : Fin q → ℝ, (∀ i, 0 ≤ x i) ∧ ∃ s : Fin p → ℝ, (∀ j, 0 ≤ s j) ∧
    ∃ r : ℝ, 0 ≤ r ∧ zw.1 = M.mulVec x + s ∧ zw.2 = e ⬝ᵥ x - r}

end Farkas
end Convex.LPDuality
