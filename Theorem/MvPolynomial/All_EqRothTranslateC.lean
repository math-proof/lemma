module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.NumberTheory.RothAuxiliary.Part7
open MathlibExt.NumberTheory.RothAuxiliary


public section

/--
[rothTranslate_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  [CommRing S]
  {m : ℕ} (x : Fin m → S) (c : S) :
-- imply
  rothTranslate m x (MvPolynomial.C c) = MvPolynomial.C c := by
-- proof
  induction m with
  | zero =>
    simp [rothTranslate]
  | succ n ih =>
    have hC :
      MvPolynomial.finSuccEquiv S n (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) := by
      change (MvPolynomial.finSuccEquiv S n) (algebraMap S _ c) =
        Polynomial.C (algebraMap S _ c)
      apply (MvPolynomial.finSuccEquiv S n).commutes c
    apply (MvPolynomial.finSuccEquiv S n).injective
    simp [rothTranslate, hC, ih]


-- created on 2026-10-21
-- updated on 2026-11-15
