import sympy.Basic


/--
determine the cardinality of List.Vector α n given α is of Fintype
-/
@[main]
private lemma main
  [Fintype ι]
-- given
  (n : ℕ) :
-- imply
  Fintype.card (List.Vector ι n) = Fintype.card ι ^ n := by
-- proof
  simp


-- created on 2025-05-23
