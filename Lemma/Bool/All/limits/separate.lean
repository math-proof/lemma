import Initialize.Tactic.Attr.Basic
import Lemma.Bool.All.doit.outer.setlimit


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → Prop}
  {g : ℕ → ℕ → Prop}
-- given
  (h : 0 < n) :
-- imply
  (∀ j < n, ∀ i < n, f j ∧ g i j) ↔ ∀ j < n, f j ∧ ∀ i < n, g i j := by
-- proof
  constructor
  ·
    intro h' j hj
    exact ⟨(h' j hj 0 h).1, fun i hi => (h' j hj i hi).2⟩
  ·
    intro h' j hj i hi
    exact ⟨(h' j hj).1, (h' j hj).2 i hi⟩


-- created on 2023-06-06
-- updated on 2026-11-24
