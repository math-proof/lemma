import Lemma.Basic


/--
determine the cardinality of List.Vector α n given α is of Fintype
-/
@[main]
private lemma main
  [Fintype α]
-- given
  (n : ℕ) :
-- imply
  Fintype.card (List.Vector α n) = Fintype.card α ^ n := by
-- proof
  simp


-- created on 2025-05-23
