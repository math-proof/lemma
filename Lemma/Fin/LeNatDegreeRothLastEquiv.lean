import Mathlib
import Lemma.Fin.CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex
import Lemma.Fin.EqRothLastIndex_Last.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothLastEquiv_natDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ} [CommSemiring R]
  {P : MvPolynomial (Fin (n + 1)) R} {r : Fin (n + 1) → ℕ}
-- given
  (hP : rothDegreeBoundOver P r) :
-- imply
  (rothLastEquiv R n P).natDegree ≤ r (Fin.last n) := by
-- proof
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr hne
  have hcoeff : P.coeff (rothLastIndex i a) ≠ 0 := by
    rw [← CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex]
    exact MvPolynomial.mem_support_iff.mp hi
  have hmem : rothLastIndex i a ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
  have := hP (rothLastIndex i a) hmem (Fin.last n)
  rw [EqRothLastIndex_Last.of.RothMvIndex] at this
  omega


-- created on 2026-10-21
