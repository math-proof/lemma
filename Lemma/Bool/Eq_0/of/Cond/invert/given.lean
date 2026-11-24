import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Decidable p]
-- given
  (h : ¬p) :
-- imply
  Bool.toNat p = 0 := by
-- proof
  simp [h]




-- created on 2023-11-05
-- updated on 2026-11-24
