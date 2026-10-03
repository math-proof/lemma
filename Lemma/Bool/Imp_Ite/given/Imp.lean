import Lemma.Bool.Imp_Ite.is.Imp


@[main]
private lemma main
  [Decidable p]
  {α : Type*}
  {a b c : α}
-- given
  (h : p → (if p then a else b) = c) :
-- imply
  p → a = c := by
-- proof
  exact Bool.Imp.of.Imp_Ite h


-- created on 2026-10-03
