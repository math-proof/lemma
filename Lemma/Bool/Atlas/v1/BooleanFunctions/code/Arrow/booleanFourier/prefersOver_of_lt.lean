import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.Arrow
open BooleanFourier


/--
[prefersOver_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {σ : Equiv.Perm (Fin m)}
  {a b : Fin m}
-- given
  (h : σ a < σ b) :
-- imply
  prefersOver σ a b = true := by
-- proof
  simp [prefersOver, h]


lemma BooleanFourier.prefersOver_of_lt
  {m : ℕ}
  {σ : Equiv.Perm (Fin m)}
  {a b : Fin m}
-- given
  (h : σ a < σ b) :
-- imply
  prefersOver σ a b = true :=
-- proof
  main h


-- created on 2026-10-23
-- updated on 2026-11-24
