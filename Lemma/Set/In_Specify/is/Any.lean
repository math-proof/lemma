import Mathlib
import sympy.Basic
import sympy.analysis.Section_3_1
import Lemma.Set.IffVal.in.Specify
import Lemma.Set.In.of.In_Specify
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Set


/--
[SetTheory.Set.specification_axiom''](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {A:Chapter3.Set}
  {x:Object}
-- given
  (P: A → Prop) :
-- imply
  x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩ :=
-- proof
  by
    constructor
    ·
      intro h
      use In.of.In_Specify h
      simp [←IffVal.in.Specify P, h]
    intro ⟨ h, hP ⟩
    simpa [←IffVal.in.Specify P] using hP


-- created on 2026-10-22
-- updated on 2026-10-23
