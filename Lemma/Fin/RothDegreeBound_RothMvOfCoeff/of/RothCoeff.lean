import Mathlib
import Lemma.Fin.EqRothBoxIndex.of.RothBox
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvOfCoeff_degreeBound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {r : Fin m → ℕ}
-- given
  (c : RothCoeff r) :
-- imply
  rothDegreeBound (rothMvOfCoeff c) r := by
-- proof
  classical
  intro i hi h
  by_contra hnot
  have hgt : r h < i h := Nat.lt_of_not_ge hnot
  apply (MvPolynomial.mem_support_iff.mp hi : (rothMvOfCoeff c).coeff i ≠ 0)
  simp only [rothMvOfCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j _
  have hne : rothBoxIndex j ≠ i := by
    intro heq
    have := congrArg (fun k : RothMvIndex m ↦ k h) heq
    simp only [EqRothBoxIndex.of.RothBox] at this
    have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
    omega
  simp [hne]


-- created on 2026-10-21
