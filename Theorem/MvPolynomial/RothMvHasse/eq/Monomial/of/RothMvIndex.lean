module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.NumberTheory.RothAuxiliary.Part7
open MathlibExt.NumberTheory.RothAuxiliary


public section

/--
[rothMvHasse_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  {m : ℕ} [CommSemiring R]
  (i j : RothMvIndex m) (c : R) :
-- imply
  rothMvHasse i (MvPolynomial.monomial j c) =
    MvPolynomial.monomial (j - i) ((∏ h, (Nat.choose (j h) (i h) : R)) * c) := by
-- proof
  simp [rothMvHasse]


-- created on 2026-10-21
-- updated on 2026-11-15
