import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvVanishesBelow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  (x : Fin m → R) (r : Fin m → ℕ) (t : ℝ) :
-- imply
  rothMvVanishesBelow (0 : MvPolynomial (Fin m) R) x r t := by
-- proof
  intro i _
  simp


-- updated on 2026-11-13
-- created on 2026-10-21
