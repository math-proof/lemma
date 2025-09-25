import Lemma.Basic


@[main]
private lemma main
  [Div α]
-- given
  (a b : α) :
-- imply
  Div.div a b = a / b := by
-- proof
  simp [HDiv.hDiv]


-- created on 2025-09-25
