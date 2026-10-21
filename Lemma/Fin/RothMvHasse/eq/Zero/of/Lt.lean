import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvHasse_eq_zero_of_exponent_gt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r)
  {i : RothMvIndex m} {h : Fin m}
  (hi : r h < i h) :
-- imply
  rothMvHasse i P = 0 := by
-- proof
  ext k
  rw [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have hnot : k + i ∉ P.support := by
    intro hmem
    have := hP (k + i) hmem h
    simp only [Finsupp.add_apply] at this
    omega
  rw [MvPolynomial.notMem_support_iff.mp hnot, mul_zero]


-- created on 2026-10-21
