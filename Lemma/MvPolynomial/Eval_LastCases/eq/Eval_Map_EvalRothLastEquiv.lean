import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothLastEquiv_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ} [CommSemiring S]
  (x : Fin n → S) (y : S) (P : MvPolynomial (Fin (n + 1)) S) :
-- imply
  MvPolynomial.eval (Fin.lastCases y x) P =
    Polynomial.eval y
      (Polynomial.map (MvPolynomial.eval x) (rothLastEquiv S n P)) := by
-- proof
  have h := MvPolynomial.optionEquivLeft_elim_eval S (Fin n) x y
    ((MvPolynomial.renameEquiv S finSuccEquivLast) P)
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename] at h
  change MvPolynomial.eval _ P = _ at h
  have hfun :
    (fun z : Fin (n + 1) ↦ Fin.lastCases y x z) =
      (fun z : Option (Fin n) ↦ z.elim y x) ∘ finSuccEquivLast := by
    funext z
    refine Fin.lastCases ?_ (fun j ↦ ?_) z <;> simp
  rw [hfun]
  simpa [rothLastEquiv] using h


-- created on 2026-10-21
