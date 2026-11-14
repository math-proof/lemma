import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvVanishesBelow_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
-- given
  (hP : rothMvVanishesBelow P x r t) :
-- imply
  rothMvVanishesBelow (-P) x r t := by
-- proof
  intro i hi
  rw [map_neg, MvPolynomial.coeff_neg, hP i hi, neg_zero]


-- updated on 2026-11-13
-- created on 2026-10-21
