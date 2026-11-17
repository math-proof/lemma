module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvVanishesBelow_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvVanishesBelow.of.Le
  {m : ℕ} [CommRing R]
  {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
-- given
  (hP : rothMvVanishesBelow P x r a)
  (hba : b ≤ a) :
-- imply
  rothMvVanishesBelow P x r b := by
-- proof
  intro i hi
  exact hP i (hi.trans_le hba)


-- updated on 2026-11-13
-- created on 2026-10-21
