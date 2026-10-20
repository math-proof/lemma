import Mathlib.FieldTheory.KummerExtension
import sympy.Basic
open Polynomial


private lemma irreducible_X_pow_sub_C
  {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] {f : F}
  (hf : ∀ g : F, g ^ p ≠ f) :
  Irreducible (X ^ p - C f) := by
  apply X_pow_sub_C_irreducible_of_prime hp.out hf

/--
[AlgebraicCurve_KummerCover_finrank_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_KummerCover_finrank_eq.lean)
-/
@[path]
private lemma main
  [Field F] [Field L] [Algebra F L]
  {p : ℕ} {f : F} [hp : Fact p.Prime] [IsSplittingField F L (X ^ p - C f)]
-- given
  (hζ : (primitiveRoots p F).Nonempty)
  (hf : ∀ g : F, g ^ p ≠ f) :
-- imply
  Module.finrank F L = p := by
-- proof
  apply finrank_of_isSplittingField_X_pow_sub_C hζ (irreducible_X_pow_sub_C hf)


-- created on 2026-10-20
