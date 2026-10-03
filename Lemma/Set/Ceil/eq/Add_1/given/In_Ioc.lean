import sympy.sets.sets
import sympy.Basic
open Set


@[main]
private lemma main
  {x : ℝ}
  {a : ℤ}
-- given
  (h : ⌈x⌉ = a + 1) :
-- imply
  ⌈x⌉ ∈ Ioc a (a + 1) := by
-- proof
  rw [h]
  exact Set.mem_Ioc.mpr ⟨by omega, le_refl _⟩


-- created on 2023-05-29
