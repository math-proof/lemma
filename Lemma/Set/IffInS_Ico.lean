import sympy.sets.sets
import Lemma.Set.In_Ico.is.In_IocSubS
import Lemma.Set.Ioc.eq.Ico
open Set


@[main]
private lemma main
-- given
  (c a b x : ℤ) :
-- imply
  x ∈ Ico a b ↔ c - x ∈ Ico (c - b + 1) (c - a + 1) := by
-- proof
  rw [In_Ico.is.In_IocSubS c]
  rw [Ioc.eq.Ico]


-- created on 2025-09-30
