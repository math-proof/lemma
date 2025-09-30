import sympy.sets.sets
import Lemma.Algebra.LeAdd_1.of.Lt
import Lemma.Algebra.Lt_Add_1.of.Le
import Lemma.Algebra.Lt.of.LeAdd_1
import Lemma.Algebra.Le.of.Lt_Add_1
open Algebra


@[main]
private lemma main
  [IntegerRing ι]
-- given
  (a b c : ι) :
-- imply
  Ioc (c - b) (c - a) = Ico (c - b + 1) (c - a + 1) := by
-- proof
  apply Set.ext
  intro x
  simp [Set.mem_Ioc, Set.mem_Ico]
  constructor
  · 
    intro ⟨h_lt, h_le⟩
    constructor
    · 
      apply LeAdd_1.of.Lt
      assumption
    · 
      apply Lt_Add_1.of.Le
      assumption
  · 
    intro ⟨h_lt, h_le⟩
    constructor
    · 
      apply Lt.of.LeAdd_1
      assumption
    · 
      apply Le.of.Lt_Add_1
      assumption


-- created on 2025-09-30
