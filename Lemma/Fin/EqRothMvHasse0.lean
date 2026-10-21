import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvHasse_zero_index](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  (P : MvPolynomial (Fin m) R) :
-- imply
  rothMvHasse 0 P = P := by
-- proof
  classical
  unfold rothMvHasse
  calc
    _ = P.coeff.sum (fun j c ↦ MvPolynomial.monomial j c) := by
      apply Finsupp.sum_congr
      intro j _
      congr 2
      ·
        ext h
        simp
      ·
        simp
    _ = P := by
      rw [Finsupp.sum]
      simpa [MvPolynomial.support] using MvPolynomial.support_sum_monomial_coeff P


-- created on 2026-10-21
