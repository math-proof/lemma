import Mathlib
import Lemma.Fin.CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex
import Lemma.Fin.EqRothLastIndexCastSucc.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothLastEquiv_coeff_degreeBound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ} [CommSemiring R]
  {P : MvPolynomial (Fin (n + 1)) R} {r : Fin (n + 1) → ℕ}
-- given
  (hP : rothDegreeBoundOver P r)
  (a : ℕ) :
-- imply
  rothDegreeBoundOver ((rothLastEquiv R n P).coeff a) (fun h ↦ r h.castSucc) := by
-- proof
  intro i hi h
  have hcoeff : P.coeff (rothLastIndex i a) ≠ 0 := by
    rw [← CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex]
    exact MvPolynomial.mem_support_iff.mp hi
  simpa [EqRothLastIndexCastSucc.of.RothMvIndex] using
    hP (rothLastIndex i a) (MvPolynomial.mem_support_iff.mpr hcoeff) h.castSucc


-- created on 2026-10-21
