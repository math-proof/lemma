import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothDegreeBoundOver_hasse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r)
  (i : RothMvIndex m) :
-- imply
  rothDegreeBoundOver (rothMvHasse i P) r := by
-- proof
  intro k hk h
  have hcoeff := MvPolynomial.mem_support_iff.mp hk
  rw [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex] at hcoeff
  have hPk : P.coeff (k + i) ≠ 0 := by
    intro hz
    apply hcoeff
    rw [hz, mul_zero]
  apply (Nat.le_add_right (k h) (i h)).trans
  apply hP (k + i) _ h
  ·
    apply MvPolynomial.mem_support_iff.mpr hPk


-- created on 2026-10-21
