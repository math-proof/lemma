import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvVanishesBelow_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  {P Q : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
-- given
  (hP : rothMvVanishesBelow P x r t)
  (hQ : rothMvVanishesBelow Q x r t) :
-- imply
  rothMvVanishesBelow (P + Q) x r t := by
-- proof
  intro i hi
  rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP i hi, hQ i hi, add_zero]


-- updated on 2026-11-13
-- created on 2026-10-21
