module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothDegreeBoundOver_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothDegreeBoundOver_Map
  {m : ℕ} [CommSemiring R] [CommSemiring S]
  (f : R →+* S) {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ}
-- given
  (hP : rothDegreeBoundOver P r) :
-- imply
  rothDegreeBoundOver (MvPolynomial.map f P) r := by
-- proof
  intro k hk h
  apply hP k (MvPolynomial.support_map_subset f P hk)


-- updated on 2026-11-13
-- created on 2026-10-21
