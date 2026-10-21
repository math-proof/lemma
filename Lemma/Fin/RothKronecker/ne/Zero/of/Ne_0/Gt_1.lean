import Mathlib
import Lemma.Fin.RothKronecker.eq.Sum_Monomial
import Lemma.Fin.Eq.of.EqRothKroneckerEncode.All_Lt.All_Lt.Gt_1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothKronecker_ne_zero_of_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m D : ℕ} [Field K]
-- given
  (hD : 1 < D)
  {P : MvPolynomial (Fin m) K}
  (hP : P ≠ 0)
  (hb : rothKroneckerBounded D P) :
-- imply
  rothKronecker D P ≠ 0 := by
-- proof
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr hP
  have hci : P.coeff i ≠ 0 := MvPolynomial.mem_support_iff.mp hi
  have hcoeff : (rothKronecker D P).coeff (rothKroneckerEncode D fun h ↦ i h) =
      P.coeff i := by
    rw [RothKronecker.eq.Sum_Monomial, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    ·
      simp
    ·
      intro j hj hji
      have henc : rothKroneckerEncode D (fun h ↦ j h) ≠
          rothKroneckerEncode D (fun h ↦ i h) := by
        intro heq
        apply hji
        apply Finsupp.ext
        intro h
        exact congrFun
          (Eq.of.EqRothKroneckerEncode.All_Lt.All_Lt.Gt_1
            hD (hb j hj) (hb i hi) heq) h
      simp [henc]
    ·
      exact fun hnot ↦ (hnot hi).elim
  intro hz
  have := congrArg (fun Q : Polynomial K ↦ Q.coeff (rothKroneckerEncode D fun h ↦ i h)) hz
  rw [hcoeff, Polynomial.coeff_zero] at this
  exact hci this


-- created on 2026-10-21
