import sympy.sets.sets
import Lemma.Set.InAdd.of.In_Icc
import Lemma.Algebra.EqAddSub
open Set Algebra


/--
This lemma asserts that in an ordered additive commutative group, an element `x` lies within the closed interval `[a, b]` if and only if `x - d` lies within the shifted interval `[a - d, b - d]`.
This equivalence is fundamental for understanding how interval endpoints behave under translation by a constant element `d`.
-/
@[main, comm, mp, mpr]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  (x a b d : α) :
-- imply
  x ∈ Icc a b ↔ x - d ∈ Icc (a - d) (b - d) := by
-- proof
  constructor <;>
    intro h
  ·
    simp_all [Set.mem_Icc]
  ·
    have h := InAdd.of.In_Icc h d
    simp only [EqAddSub] at h
    assumption


-- created on 2025-05-12
