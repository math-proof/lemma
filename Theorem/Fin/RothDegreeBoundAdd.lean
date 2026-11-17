module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothDegreeBound_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothDegreeBoundAdd
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


-- updated on 2026-11-13
-- created on 2026-10-21
