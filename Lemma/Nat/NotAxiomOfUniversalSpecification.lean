import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_3_2
open Chapter3 hiding Nat Set


/--
[Russells_paradox](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_2.lean)
-/
@[path]
private lemma main
  [SetTheory] :
-- imply
  ¬ axiom_of_universal_specification :=
-- proof
  by
    intro h
    set P : Object → Prop := fun x ↦ ∃ X:Chapter3.Set, x = X ∧ x ∉ X
    choose Ω hΩ using h P
    if h : (Ω:Object) ∈ Ω then
      have : P (Ω:Object) := (hΩ _).mp h
      obtain ⟨Ω', ⟨hΩ1, hΩ2⟩⟩ := this
      simp at hΩ1
      rw [←hΩ1] at hΩ2
      contradiction
    else
      have : P (Ω:Object) := by use Ω
      rw [←hΩ] at this
      contradiction


-- created on 2026-10-22
-- updated on 2026-10-26
