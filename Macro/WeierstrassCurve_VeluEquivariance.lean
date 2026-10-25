import Mathlib.Algebra.Polynomial.Bivariate

/-!
# `map_simp` tactic macro

Carved from `Lemma.Definitions.Def_WeierstrassCurve_VeluEquivariance`.
The simp lemmas are resolved in this module.
-/

open Polynomial
open scoped Polynomial.Bivariate

/-- `map_simp` tactic macro. -/
macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])
