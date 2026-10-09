import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h : x ∈ Set.Ioc a b) :
-- imply
  Set.Ioc a b = Set.Ioc a x ∪ Set.Ioc x b := by
-- proof
  obtain ⟨hax, hxb⟩ := Set.mem_Ioc.mp h
  exact (Set.Ioc_union_Ioc_eq_Ioc hax.le hxb).symm


-- created on 2020-11-22
