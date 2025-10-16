import sympy.sets.sets
import Lemma.Nat.LeAdd_1.of.Lt
import Lemma.Nat.Lt_Add_1.of.Le
import Lemma.Nat.Lt.of.LeAdd_1
import Lemma.Nat.Le.of.Lt_Add_1
open Nat


@[main]
private lemma main
  [IntegerRing ι]
-- given
  (a b : ι) :
-- imply
  Ioc a b = Ico (a + 1) (b + 1) := by
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
