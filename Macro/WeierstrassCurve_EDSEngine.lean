import Mathlib.Algebra.Polynomial.Bivariate

/-!
# `C_simp` tactic macro

Carved from `Lemma.Definitions.Def_WeierstrassCurve_EDSEngine`.
The simp lemmas are resolved in this module.
-/

open Polynomial
open scoped Polynomial.Bivariate

/-- `C_simp` tactic macro. -/
macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])
