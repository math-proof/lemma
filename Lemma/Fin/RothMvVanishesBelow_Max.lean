import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvVanishesBelow_max](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
-- given
  (ha : rothMvVanishesBelow P x r a)
  (hb : rothMvVanishesBelow P x r b) :
-- imply
  rothMvVanishesBelow P x r (max a b) := by
-- proof
  obtain hab | hba := le_total a b
  · simpa [max_eq_right hab] using hb
  · simpa [max_eq_left hba] using ha


-- created on 2026-10-21
