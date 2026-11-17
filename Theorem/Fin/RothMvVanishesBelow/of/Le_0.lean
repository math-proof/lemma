module

public import Mathlib
public import Theorem.Fin.RothMvWeight.ge.Zero.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvVanishesBelow_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvVanishesBelow.of.Le_0
  {m : ℕ} [CommRing R]
  (P : MvPolynomial (Fin m) R) (x : Fin m → R) (r : Fin m → ℕ)
  {t : ℝ}
-- given
  (ht : t ≤ 0) :
-- imply
  rothMvVanishesBelow P x r t := by
-- proof
  intro i hi
  exact (not_lt_of_ge (RothMvWeight.ge.Zero.of.RothMvIndex r i) (hi.trans_le ht)).elim


-- created on 2026-10-21
