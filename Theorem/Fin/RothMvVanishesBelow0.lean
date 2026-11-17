module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvVanishesBelow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvVanishesBelow0
  {m : ℕ} [CommRing R]
  (x : Fin m → R) (r : Fin m → ℕ) (t : ℝ) :
-- imply
  rothMvVanishesBelow (0 : MvPolynomial (Fin m) R) x r t := by
-- proof
  intro i _
  simp


-- updated on 2026-11-13
-- created on 2026-10-21
