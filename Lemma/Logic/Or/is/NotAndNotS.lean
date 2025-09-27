import Lemma.Basic


@[main, mp, mpr]
private lemma main
  [Decidable a]
  [Decidable b] :
-- imply
  a ∨ b ↔ ¬(¬a ∧ ¬b) :=
-- proof
  Decidable.or_iff_not_not_and_not


-- created on 2025-03-29
