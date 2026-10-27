import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.MathlibExtTest.NumberTheory.AppellSequence
open MetaMathlibExt


/--
[monomial_isAppell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AppellSequence.lean)
-/
@[path]
private lemma monomial_isAppell : IsAppellSequence monomialSeq := by
  constructor
  · intro n
    simp [monomialSeq]
  · intro n
    simp [monomialSeq]

/--
[deg_check0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AppellSequence.lean)
-/
@[path]
private lemma deg_check0 : (monomialSeq 0).degree = 0 :=
  monomial_isAppell.1 0

/--
[deg_check1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AppellSequence.lean)
-/
@[path]
private lemma deg_check1 : (monomialSeq 1).degree = 1 :=
  monomial_isAppell.1 1

/--
[deriv_check0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AppellSequence.lean)
-/
@[path]
private lemma deriv_check0 :
  Polynomial.derivative (monomialSeq 1) =
    Polynomial.C ((0 + 1 : ℕ) : ℚ) * monomialSeq 0 :=
  monomial_isAppell.2 0

/--
[deriv_check1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AppellSequence.lean)
-/
@[path]
private lemma deriv_check1 :
  Polynomial.derivative (monomialSeq 2) =
    Polynomial.C ((1 + 1 : ℕ) : ℚ) * monomialSeq 1 :=
  monomial_isAppell.2 1

/--
[zero_not_appell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AppellSequence.lean)
-/
@[path]
private lemma zero_not_appell : ¬IsAppellSequence zeroSeq := by
  intro h
  have h0 := h.1 0
  simp [zeroSeq] at h0


-- created on 2026-10-23
