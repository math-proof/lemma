import sympy.sets.fancysets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.In_Range.is.Any_Eq_AddMul |
| comm | Int.Any_Eq_AddMul.is.In_Range |
| mp | Int.Any_Eq_AddMul.of.In_Range |
| mpr | Int.In_Range.of.Any_Eq_AddMul |
-/
@[main, comm, mp, mpr]
private lemma main
  {x a b d : ℤ} :
-- imply
  x ∈ Range a b d ↔
    ∃ k ∈ List.range (((b - a) * d.sign + |d| - 1) / |d|).toNat,
      x = a + (k : ℤ) * d := by
-- proof
  simp [Range, List.mem_map, List.mem_range, eq_comm]


-- created on 2026-09-06
