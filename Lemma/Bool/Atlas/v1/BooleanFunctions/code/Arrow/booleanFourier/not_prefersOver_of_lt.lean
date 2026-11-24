import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Arrow.booleanFourier.prefersOver_of_lt
open BooleanFourier Bool


/--
[not_prefersOver_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {σ : Equiv.Perm (Fin m)}
  {a b : Fin m}
-- given
  (h : σ b < σ a) :
-- imply
  prefersOver σ a b = false := by
-- proof
  simp [prefersOver] at h ⊢; omega


lemma BooleanFourier.not_prefersOver_of_lt
  {m : ℕ}
  {σ : Equiv.Perm (Fin m)}
  {a b : Fin m}
-- given
  (h : σ b < σ a) :
-- imply
  prefersOver σ a b = false :=
-- proof
  main h


-- created on 2026-10-23
-- updated on 2026-11-24
