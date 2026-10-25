/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Instance.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
/-!
# Projective numerator degrees for Manin's proof

This file isolates the characteristic-free commutative algebra used to recover the numerator
degrees of two rational functions from primitive projective product and sum coordinates.
-/


namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

noncomputable section

open Polynomial

universe u

variable {K : Type u} [Field K]

/-- Three homogeneous coordinates are primitive when they generate the unit ideal. -/
def PrimitiveTriple (a b c : K[X]) : Prop :=
  ∃ u v w : K[X], u * a + v * b + w * c = 1

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
