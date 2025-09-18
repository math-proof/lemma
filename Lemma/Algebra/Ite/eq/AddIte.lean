import Lemma.Basic


@[main]
private lemma main
  [Decidable p]
  [Add α]
  {a b c : α} :
-- imply
  (if p then
    a + c
  else
    b + c) = (if p then
    a
  else
    b) + c := by
-- proof
  split_ifs with h <;> rfl


-- created on 2025-04-26
-- updated on 2025-05-14
