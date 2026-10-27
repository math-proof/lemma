import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.ListColoring
open SimpleGraph


/--
[finOne_isListColorable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/ListColoring.lean)
-/
@[path]
private lemma finOne_isListColorable :
  (⊥ : SimpleGraph (Fin 1)).IsListColorable 1 := by
  intro C _ lists hlists
  have hnonempty : (lists 0).Nonempty :=
    Finset.card_pos.mp (Nat.zero_lt_one.trans_le (hlists 0))
  let c : C := hnonempty.choose
  refine ⟨⟨fun _ => c, ?_⟩, fun v => ?_⟩
  · simp
  · have hv : v = 0 := Subsingleton.elim _ _
    subst v
    exact hnonempty.choose_spec


-- created on 2026-10-23
