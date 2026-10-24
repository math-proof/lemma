import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_3
import Lemma.Set.OneToOne.is.All_Eq
import Lemma.Set.EqIffP
import Lemma.Set.EqToFn
import Lemma.Set.EqGetMkFn
open Chapter3 hiding Nat Set
open Chapter3.Function
open Set


/--
[Function.bijective_incorrect_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_3.lean)
-/
@[path]
private lemma main
  [SetTheory] :
-- imply
  ∃ X Y: Chapter3.Set, ∃ f: Function X Y, (∀ x: X, ∃! y: Y, y = f x) ∧ ¬ f.bijective :=
-- proof
  by
    use Chapter3.Nat, Chapter3.Nat
    set f := mk_fn fun x ↦ (0: Chapter3.Nat); use f
    constructor
    ·
      intros
      apply existsUnique_of_exists_of_unique
      ·
        use 0
        rw [EqIffP]
      intros; rw [EqIffP] at *; aesop
    rw [Function.bijective]
    suffices h : ¬ f.one_to_one by tauto
    rw [OneToOne.is.All_Eq]
    push_neg; use 0, 1; simp [f, EqToFn, EqGetMkFn]


-- created on 2026-10-22
-- updated on 2026-10-23
