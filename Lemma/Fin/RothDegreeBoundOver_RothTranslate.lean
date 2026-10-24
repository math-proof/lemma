import Mathlib
import Lemma.Fin.RothMvHasse.eq.Zero.of.Lt
import Lemma.Fin.CoeffRothTranslateM.eq.EvalRothMvHasse
open MathlibExt.NumberTheory.RothAuxiliary
open Fin Set


/--
[rothDegreeBoundOver_translate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r)
  (x : Fin m → R) :
-- imply
  rothDegreeBoundOver (rothTranslate m x P) r := by
-- proof
  intro i hi h
  by_contra hri
  have hgt : r h < i h := Nat.lt_of_not_ge hri
  have hzero : rothMvHasse i P = 0 := RothMvHasse.eq.Zero.of.Lt hP hgt
  have hcoeff := MvPolynomial.mem_support_iff.mp hi
  rw [CoeffRothTranslateM.eq.EvalRothMvHasse, hzero, map_zero] at hcoeff
  exact hcoeff rfl


-- created on 2026-10-21
