import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_3_1.Part5
import Lemma.Set.IffVal.in.Specify
import Lemma.Set.In.of.In_Specify
open Chapter3.SetTheory.Set
open Chapter3 hiding Nat Set
open Chapter3.SetTheory
open Set


/--
[SetTheory.Set.mem_sdiff](https://github.com/teorth/analysis/blob/main/Analysis/Section_3_1.lean)
-/
@[path]
private lemma main
  [SetTheory]
  {x:Object}
  {X Y:Chapter3.Set} :
-- imply
  x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) :=
-- proof
  by
    constructor
    ·
      intro h
      have h' := In.of.In_Specify h
      simp [h']
      exact (IffVal.in.Specify (x := ⟨x, h'⟩) _).mp h
    intro ⟨ hX, hY ⟩
    exact (IffVal.in.Specify (x := ⟨x, hX⟩) (fun x ↦ x.val ∉ Y)).mpr hY


-- created on 2026-10-22
-- updated on 2026-10-26
