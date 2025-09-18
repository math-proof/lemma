import Lemma.Basic


@[main]
private lemma main
  [Decidable p]
-- given
  (F G H : Set α) :
-- imply
  H ∩ (if p then
    F
  else
    G) = if p then
    H ∩ F
  else
    H ∩ G := by
-- proof
  aesop


-- created on 2025-08-02
