/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
/-!
# Jaccard distance triangle inequality on arbitrary lattices

Generalized Jaccard distance from a real-valued lattice valuation, following
`https://arxiv.org/abs/2608.18194v1` (Badica–Badica).

Scope: arbitrary lattices with no distributivity, complements, bounds,
finiteness, or strict monotonicity. Proves the Gilbert condition is equivalent
to modularity plus monotonicity, and the triangle inequality from the Gilbert
condition (hence for strictly positive monotone modular valuations). This is a
triangle inequality only, not a `PseudoMetricSpace` instance.
-/


namespace JaccardLattice

variable {L : Type*} [Lattice L]

/-- Modularity of a real-valued lattice valuation. -/
def IsModularValuation (f : L → ℝ) : Prop :=
  ∀ X Y, f X + f Y = f (X ⊔ Y) + f (X ⊓ Y)

/-- Strict positivity of a real-valued lattice valuation. -/
def IsStrictlyPositive (f : L → ℝ) : Prop :=
  ∀ X, 0 < f X

/-- Gilbert condition for a real-valued lattice valuation. -/
def GilbertCondition (f : L → ℝ) : Prop :=
  ∀ X Y Z, f (X ⊔ Z) + f (Z ⊔ Y) + f (X ⊓ Y) ≥
    f (X ⊓ Z) + f (Z ⊓ Y) + f (X ⊔ Y ⊔ Z)

/-- Generalized Jaccard distance from a real-valued lattice valuation. -/
noncomputable def jaccardDist (f : L → ℝ) (X Y : L) : ℝ :=
  1 - f (X ⊓ Y) / f (X ⊔ Y)

end JaccardLattice
