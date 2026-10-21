import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothDegreeBound_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {P Q : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBound P r)
  (hQ : rothDegreeBound Q r) :
-- imply
  rothDegreeBound (P + Q) r := by
-- proof
  intro i hi h
  obtain hiP | hiQ := Finset.mem_union.mp (MvPolynomial.support_add hi)
  · exact hP i hiP h
  · exact hQ i hiQ h


-- created on 2026-10-21
