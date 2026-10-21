import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvVanishesBelow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  (x : Fin m → R) (r : Fin m → ℕ) (t : ℝ) :
-- imply
  rothMvVanishesBelow (0 : MvPolynomial (Fin m) R) x r t := by
-- proof
  intro i _
  simp


-- created on 2026-10-21
