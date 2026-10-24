import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
import Lemma.Set.EqIffP
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.eq_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {X Y: Chapter3.Set}
  {f g: Function X Y} :
-- imply
  f = g ↔ ∀ x: X, f x = g x :=
-- proof
  by
    constructor <;> intro h
    ·
      simp [h]
    ext x y; constructor <;> intros
    ·
      rwa [←EqIffP, ←h x, EqIffP]
    rwa [←EqIffP, h x, EqIffP]


-- created on 2026-10-22
-- updated on 2026-10-23
