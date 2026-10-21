import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvVanishesBelow_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
-- given
  (hP : rothMvVanishesBelow P x r a)
  (hba : b ≤ a) :
-- imply
  rothMvVanishesBelow P x r b := by
-- proof
  intro i hi
  exact hP i (hi.trans_le hba)


-- created on 2026-10-21
