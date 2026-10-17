import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Set.In_Icc.is.AndLe__Ge |
| comm | Set.AndLe__Ge.is.In_Icc |
| mp | Set.AndLe__Ge.of.In_Icc |
| mpr | Set.In_Icc.of.AndLe__Ge |
-/
@[path, comm, mp, mpr]
private lemma main
  {a b x : ℝ} :
-- imply
  x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b :=
-- proof
  Set.mem_Icc


-- created on 2026-10-11
-- updated on 2026-10-17
